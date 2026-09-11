import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyTwoCBFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyTwoCBFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyTwoCBFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyTwoCBFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyTwoCBFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyTwoCBFastPow a n * eightyTwoCBFastPow a n * a else eightyTwoCBFastPow a n * eightyTwoCBFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyTwoCB_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyTwoCB_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyTwoCB_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyTwoCB_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyTwoCB_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyTwoCB_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyTwoCB_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyTwoCB_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyTwoCB_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyTwoCB_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyTwoCB_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyTwoCB_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyTwoCB_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyTwoCB_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyTwoCB_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyTwoCB_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyTwoCB_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyTwoCB_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyTwoCB_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyTwoCB_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyTwoCB_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyTwoCB_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyTwoCB_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyTwoCB_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyTwoCB_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyTwoCB_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyTwoCB_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyTwoCB_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyTwoCB_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyTwoCB_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyTwoCB_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyTwoCB_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyTwoCB_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyTwoCB_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyTwoCB_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyTwoCB_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyTwoCB_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyTwoCB_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyTwoCB_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyTwoCB_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightyTwoCB_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyTwoCB_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightyTwoCB_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyTwoCB_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightyTwoCB_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightyTwoCB_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyTwoCB_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightyTwoCB_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyTwoCB_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightyTwoCB_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightyTwoCB_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightyTwoCB_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightyTwoCB_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightyTwoCB_257 : Nat.Prime 257 := by norm_num

private theorem prime_eightyTwoCB_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyTwoCB_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyTwoCB_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightyTwoCB_283 : Nat.Prime 283 := by norm_num

private theorem prime_eightyTwoCB_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightyTwoCB_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyTwoCB_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightyTwoCB_337 : Nat.Prime 337 := by norm_num

private theorem prime_eightyTwoCB_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightyTwoCB_353 : Nat.Prime 353 := by norm_num

private theorem prime_eightyTwoCB_359 : Nat.Prime 359 := by norm_num

private theorem prime_eightyTwoCB_367 : Nat.Prime 367 := by norm_num

private theorem prime_eightyTwoCB_373 : Nat.Prime 373 := by norm_num

private theorem prime_eightyTwoCB_379 : Nat.Prime 379 := by norm_num

private theorem prime_eightyTwoCB_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyTwoCB_389 : Nat.Prime 389 := by norm_num

private theorem prime_eightyTwoCB_439 : Nat.Prime 439 := by norm_num

private theorem prime_eightyTwoCB_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightyTwoCB_491 : Nat.Prime 491 := by norm_num

private theorem prime_eightyTwoCB_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightyTwoCB_509 : Nat.Prime 509 := by norm_num

private theorem prime_eightyTwoCB_521 : Nat.Prime 521 := by norm_num

private theorem prime_eightyTwoCB_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyTwoCB_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightyTwoCB_569 : Nat.Prime 569 := by norm_num

private theorem prime_eightyTwoCB_571 : Nat.Prime 571 := by norm_num

private theorem prime_eightyTwoCB_593 : Nat.Prime 593 := by norm_num

private theorem prime_eightyTwoCB_601 : Nat.Prime 601 := by norm_num

private theorem prime_eightyTwoCB_613 : Nat.Prime 613 := by norm_num

private theorem prime_eightyTwoCB_617 : Nat.Prime 617 := by norm_num

private theorem prime_eightyTwoCB_619 : Nat.Prime 619 := by norm_num

private theorem prime_eightyTwoCB_631 : Nat.Prime 631 := by norm_num

private theorem prime_eightyTwoCB_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightyTwoCB_643 : Nat.Prime 643 := by norm_num

private theorem prime_eightyTwoCB_673 : Nat.Prime 673 := by norm_num

private theorem prime_eightyTwoCB_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightyTwoCB_719 : Nat.Prime 719 := by norm_num

private theorem prime_eightyTwoCB_727 : Nat.Prime 727 := by norm_num

private theorem prime_eightyTwoCB_733 : Nat.Prime 733 := by norm_num

private theorem prime_eightyTwoCB_739 : Nat.Prime 739 := by norm_num

private theorem prime_eightyTwoCB_761 : Nat.Prime 761 := by norm_num

private theorem prime_eightyTwoCB_811 : Nat.Prime 811 := by norm_num

private theorem prime_eightyTwoCB_827 : Nat.Prime 827 := by norm_num

private theorem prime_eightyTwoCB_839 : Nat.Prime 839 := by norm_num

private theorem prime_eightyTwoCB_853 : Nat.Prime 853 := by norm_num

private theorem prime_eightyTwoCB_881 : Nat.Prime 881 := by norm_num

private theorem prime_eightyTwoCB_919 : Nat.Prime 919 := by norm_num

private theorem prime_eightyTwoCB_983 : Nat.Prime 983 := by norm_num

private theorem prime_eightyTwoCB_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_eightyTwoCB_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_eightyTwoCB_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_eightyTwoCB_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_eightyTwoCB_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightyTwoCB_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_eightyTwoCB_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_eightyTwoCB_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_eightyTwoCB_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_eightyTwoCB_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_eightyTwoCB_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_eightyTwoCB_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_eightyTwoCB_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightyTwoCB_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_eightyTwoCB_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_eightyTwoCB_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_eightyTwoCB_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_eightyTwoCB_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_eightyTwoCB_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_eightyTwoCB_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_eightyTwoCB_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_eightyTwoCB_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_eightyTwoCB_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_eightyTwoCB_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_eightyTwoCB_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_eightyTwoCB_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_eightyTwoCB_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_eightyTwoCB_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_eightyTwoCB_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_eightyTwoCB_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_eightyTwoCB_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_eightyTwoCB_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_eightyTwoCB_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_eightyTwoCB_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_eightyTwoCB_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_eightyTwoCB_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_eightyTwoCB_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_eightyTwoCB_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_eightyTwoCB_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_eightyTwoCB_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_eightyTwoCB_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_eightyTwoCB_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_eightyTwoCB_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_eightyTwoCB_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_eightyTwoCB_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_eightyTwoCB_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_eightyTwoCB_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_eightyTwoCB_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_eightyTwoCB_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_eightyTwoCB_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_eightyTwoCB_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_eightyTwoCB_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_eightyTwoCB_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_eightyTwoCB_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_eightyTwoCB_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_eightyTwoCB_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_eightyTwoCB_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_eightyTwoCB_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_eightyTwoCB_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_eightyTwoCB_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_eightyTwoCB_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_eightyTwoCB_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_eightyTwoCB_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_eightyTwoCB_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_eightyTwoCB_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_eightyTwoCB_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_eightyTwoCB_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_eightyTwoCB_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_eightyTwoCB_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_eightyTwoCB_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_eightyTwoCB_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_eightyTwoCB_4463 : Nat.Prime 4463 := by norm_num

private theorem prime_eightyTwoCB_4759 : Nat.Prime 4759 := by norm_num

private theorem prime_eightyTwoCB_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_eightyTwoCB_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_eightyTwoCB_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_eightyTwoCB_5153 : Nat.Prime 5153 := by norm_num

private theorem prime_eightyTwoCB_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_eightyTwoCB_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_eightyTwoCB_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_eightyTwoCB_5827 : Nat.Prime 5827 := by norm_num

private theorem prime_eightyTwoCB_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_eightyTwoCB_6329 : Nat.Prime 6329 := by norm_num

private theorem prime_eightyTwoCB_6469 : Nat.Prime 6469 := by norm_num

private theorem prime_eightyTwoCB_6553 : Nat.Prime 6553 := by norm_num

private theorem prime_eightyTwoCB_6763 : Nat.Prime 6763 := by norm_num

private theorem prime_eightyTwoCB_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_eightyTwoCB_6823 : Nat.Prime 6823 := by norm_num

private theorem prime_eightyTwoCB_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_eightyTwoCB_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_eightyTwoCB_7331 : Nat.Prime 7331 := by norm_num

private theorem prime_eightyTwoCB_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_eightyTwoCB_7621 : Nat.Prime 7621 := by norm_num

private theorem prime_eightyTwoCB_7727 : Nat.Prime 7727 := by norm_num

private theorem prime_eightyTwoCB_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_eightyTwoCB_7927 : Nat.Prime 7927 := by norm_num

private theorem prime_eightyTwoCB_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_eightyTwoCB_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_eightyTwoCB_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_eightyTwoCB_8179 : Nat.Prime 8179 := by norm_num

private theorem prime_eightyTwoCB_8389 : Nat.Prime 8389 := by norm_num

private theorem prime_eightyTwoCB_8783 : Nat.Prime 8783 := by norm_num

private theorem prime_eightyTwoCB_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_eightyTwoCB_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_eightyTwoCB_9041 : Nat.Prime 9041 := by norm_num

private theorem prime_eightyTwoCB_9127 : Nat.Prime 9127 := by norm_num

private theorem prime_eightyTwoCB_9277 : Nat.Prime 9277 := by norm_num

private theorem prime_eightyTwoCB_9343 : Nat.Prime 9343 := by norm_num

private theorem prime_eightyTwoCB_10223 : Nat.Prime 10223 := by norm_num

private theorem prime_eightyTwoCB_10253 : Nat.Prime 10253 := by norm_num

private theorem prime_eightyTwoCB_10601 : Nat.Prime 10601 := by norm_num

private theorem prime_eightyTwoCB_10753 : Nat.Prime 10753 := by norm_num

private theorem prime_eightyTwoCB_11003 : Nat.Prime 11003 := by norm_num

private theorem prime_eightyTwoCB_11087 : Nat.Prime 11087 := by norm_num

private theorem prime_eightyTwoCB_11177 : Nat.Prime 11177 := by norm_num

private theorem prime_eightyTwoCB_11321 : Nat.Prime 11321 := by norm_num

private theorem prime_eightyTwoCB_11329 : Nat.Prime 11329 := by norm_num

private theorem prime_eightyTwoCB_11369 : Nat.Prime 11369 := by norm_num

private theorem prime_eightyTwoCB_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_eightyTwoCB_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_eightyTwoCB_13159 : Nat.Prime 13159 := by norm_num

private theorem prime_eightyTwoCB_13219 : Nat.Prime 13219 := by norm_num

private theorem prime_eightyTwoCB_13291 : Nat.Prime 13291 := by norm_num

private theorem prime_eightyTwoCB_13469 : Nat.Prime 13469 := by norm_num

private theorem prime_eightyTwoCB_14341 : Nat.Prime 14341 := by norm_num

private theorem prime_eightyTwoCB_14503 : Nat.Prime 14503 := by norm_num

private theorem prime_eightyTwoCB_14731 : Nat.Prime 14731 := by norm_num

private theorem prime_eightyTwoCB_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_eightyTwoCB_15187 : Nat.Prime 15187 := by norm_num

private theorem prime_eightyTwoCB_15361 : Nat.Prime 15361 := by norm_num

private theorem prime_eightyTwoCB_15377 : Nat.Prime 15377 := by norm_num

private theorem prime_eightyTwoCB_15803 : Nat.Prime 15803 := by norm_num

private theorem prime_eightyTwoCB_15881 : Nat.Prime 15881 := by norm_num

private theorem prime_eightyTwoCB_17579 : Nat.Prime 17579 := by norm_num

private theorem prime_eightyTwoCB_18131 : Nat.Prime 18131 := by norm_num

private theorem prime_eightyTwoCB_18803 : Nat.Prime 18803 := by norm_num

private theorem prime_eightyTwoCB_19031 : Nat.Prime 19031 := by norm_num

private theorem prime_eightyTwoCB_19157 : Nat.Prime 19157 := by norm_num

private theorem prime_eightyTwoCB_20231 : Nat.Prime 20231 := by norm_num

private theorem prime_eightyTwoCB_20929 : Nat.Prime 20929 := by norm_num

private theorem prime_eightyTwoCB_20981 : Nat.Prime 20981 := by norm_num

private theorem prime_eightyTwoCB_21107 : Nat.Prime 21107 := by norm_num

private theorem prime_eightyTwoCB_21163 : Nat.Prime 21163 := by norm_num

private theorem prime_eightyTwoCB_21767 : Nat.Prime 21767 := by norm_num

private theorem prime_eightyTwoCB_22063 : Nat.Prime 22063 := by norm_num

private theorem prime_eightyTwoCB_22853 : Nat.Prime 22853 := by norm_num

private theorem prime_eightyTwoCB_22859 : Nat.Prime 22859 := by norm_num

private theorem prime_eightyTwoCB_23813 : Nat.Prime 23813 := by norm_num

private theorem prime_eightyTwoCB_25219 : Nat.Prime 25219 := by norm_num

private theorem prime_eightyTwoCB_26189 : Nat.Prime 26189 := by norm_num

private theorem prime_eightyTwoCB_26449 : Nat.Prime 26449 := by norm_num

private theorem prime_eightyTwoCB_27253 : Nat.Prime 27253 := by norm_num

private theorem prime_eightyTwoCB_28549 : Nat.Prime 28549 := by norm_num

private theorem prime_eightyTwoCB_29009 : Nat.Prime 29009 := by norm_num

private theorem prime_eightyTwoCB_29927 : Nat.Prime 29927 := by norm_num

private theorem prime_eightyTwoCB_33287 : Nat.Prime 33287 := by norm_num

private theorem prime_eightyTwoCB_33767 : Nat.Prime 33767 := by norm_num

private theorem prime_eightyTwoCB_35107 : Nat.Prime 35107 := by norm_num

private theorem prime_eightyTwoCB_35969 : Nat.Prime 35969 := by norm_num

private theorem prime_eightyTwoCB_36433 : Nat.Prime 36433 := by norm_num

private theorem prime_eightyTwoCB_36637 : Nat.Prime 36637 := by norm_num

private theorem prime_eightyTwoCB_38783 : Nat.Prime 38783 := by norm_num

private theorem prime_eightyTwoCB_38839 : Nat.Prime 38839 := by norm_num

private theorem prime_eightyTwoCB_40087 : Nat.Prime 40087 := by norm_num

private theorem prime_eightyTwoCB_41231 : Nat.Prime 41231 := by norm_num

private theorem prime_eightyTwoCB_42359 : Nat.Prime 42359 := by norm_num

private theorem prime_eightyTwoCB_43711 : Nat.Prime 43711 := by norm_num

private theorem prime_eightyTwoCB_46757 : Nat.Prime 46757 := by norm_num

private theorem prime_eightyTwoCB_50543 : Nat.Prime 50543 := by norm_num

private theorem prime_eightyTwoCB_52967 : Nat.Prime 52967 := by norm_num

private theorem prime_eightyTwoCB_55243 : Nat.Prime 55243 := by norm_num

private theorem prime_eightyTwoCB_55837 : Nat.Prime 55837 := by norm_num

private theorem prime_eightyTwoCB_56737 : Nat.Prime 56737 := by norm_num

private theorem prime_eightyTwoCB_58207 : Nat.Prime 58207 := by norm_num

private theorem prime_eightyTwoCB_58337 : Nat.Prime 58337 := by norm_num

private theorem prime_eightyTwoCB_58537 : Nat.Prime 58537 := by norm_num

private theorem prime_eightyTwoCB_60457 : Nat.Prime 60457 := by norm_num

private theorem prime_eightyTwoCB_60493 : Nat.Prime 60493 := by norm_num

private theorem prime_eightyTwoCB_60727 : Nat.Prime 60727 := by norm_num

private theorem prime_eightyTwoCB_61291 : Nat.Prime 61291 := by norm_num

private theorem prime_eightyTwoCB_62819 : Nat.Prime 62819 := by norm_num

private theorem prime_eightyTwoCB_63799 : Nat.Prime 63799 := by norm_num

private theorem prime_eightyTwoCB_66593 : Nat.Prime 66593 := by norm_num

private theorem prime_eightyTwoCB_67219 : Nat.Prime 67219 := by norm_num

private theorem prime_eightyTwoCB_68171 : Nat.Prime 68171 := by norm_num

private theorem prime_eightyTwoCB_69677 : Nat.Prime 69677 := by norm_num

private theorem prime_eightyTwoCB_72937 : Nat.Prime 72937 := by norm_num

private theorem prime_eightyTwoCB_73483 : Nat.Prime 73483 := by norm_num

private theorem prime_eightyTwoCB_75577 : Nat.Prime 75577 := by norm_num

private theorem prime_eightyTwoCB_80077 : Nat.Prime 80077 := by norm_num

private theorem prime_eightyTwoCB_81163 : Nat.Prime 81163 := by norm_num

private theorem prime_eightyTwoCB_83089 : Nat.Prime 83089 := by norm_num

private theorem prime_eightyTwoCB_85601 : Nat.Prime 85601 := by norm_num

private theorem prime_eightyTwoCB_89591 : Nat.Prime 89591 := by norm_num

private theorem prime_eightyTwoCB_92723 : Nat.Prime 92723 := by norm_num

private theorem prime_eightyTwoCB_95789 : Nat.Prime 95789 := by norm_num

private theorem prime_eightyTwoCB_101081 : Nat.Prime 101081 := by norm_num

private theorem prime_eightyTwoCB_101693 : Nat.Prime 101693 := by norm_num

private theorem prime_eightyTwoCB_103423 : Nat.Prime 103423 := by norm_num

private theorem prime_eightyTwoCB_103991 : Nat.Prime 103991 := by norm_num

private theorem prime_eightyTwoCB_108023 : Nat.Prime 108023 := by norm_num

private theorem prime_eightyTwoCB_108503 : Nat.Prime 108503 := by norm_num

private theorem prime_eightyTwoCB_108799 : Nat.Prime 108799 := by norm_num

private theorem prime_eightyTwoCB_109147 : Nat.Prime 109147 := by norm_num

private theorem prime_eightyTwoCB_112643 : Nat.Prime 112643 := by norm_num

private theorem prime_eightyTwoCB_113891 : Nat.Prime 113891 := by norm_num

private theorem prime_eightyTwoCB_115763 : Nat.Prime 115763 := by norm_num

private theorem prime_eightyTwoCB_119701 : Nat.Prime 119701 := by norm_num

private theorem prime_eightyTwoCB_120349 : Nat.Prime 120349 := by norm_num

private theorem prime_eightyTwoCB_122579 : Nat.Prime 122579 := by norm_num

private theorem prime_eightyTwoCB_129671 : Nat.Prime 129671 := by norm_num

private theorem prime_eightyTwoCB_131381 : Nat.Prime 131381 := by norm_num

private theorem prime_eightyTwoCB_133351 : Nat.Prime 133351 := by norm_num

private theorem prime_eightyTwoCB_152407 : Nat.Prime 152407 := by norm_num

private theorem prime_eightyTwoCB_154369 : Nat.Prime 154369 := by norm_num

private theorem prime_eightyTwoCB_155291 : Nat.Prime 155291 := by norm_num

private theorem prime_eightyTwoCB_156749 : Nat.Prime 156749 := by norm_num

private theorem prime_eightyTwoCB_158981 : Nat.Prime 158981 := by norm_num

private theorem prime_eightyTwoCB_159403 : Nat.Prime 159403 := by norm_num

private theorem prime_eightyTwoCB_165391 : Nat.Prime 165391 := by norm_num

private theorem prime_eightyTwoCB_165587 : Nat.Prime 165587 := by norm_num

private theorem prime_eightyTwoCB_165779 : Nat.Prime 165779 := by norm_num

private theorem prime_eightyTwoCB_167081 : Nat.Prime 167081 := by norm_num

private theorem prime_eightyTwoCB_167449 : Nat.Prime 167449 := by norm_num

private theorem prime_eightyTwoCB_167801 : Nat.Prime 167801 := by norm_num

private theorem prime_eightyTwoCB_204163 : Nat.Prime 204163 := by norm_num

private theorem prime_eightyTwoCB_206369 : Nat.Prime 206369 := by norm_num

private theorem prime_eightyTwoCB_211927 : Nat.Prime 211927 := by norm_num

private theorem prime_eightyTwoCB_225427 : Nat.Prime 225427 := by norm_num

private theorem prime_eightyTwoCB_236231 : Nat.Prime 236231 := by norm_num

private theorem prime_eightyTwoCB_236339 : Nat.Prime 236339 := by norm_num

private theorem prime_eightyTwoCB_242449 : Nat.Prime 242449 := by norm_num

private theorem prime_eightyTwoCB_250867 : Nat.Prime 250867 := by norm_num

private theorem prime_eightyTwoCB_254627 : Nat.Prime 254627 := by norm_num

private theorem prime_eightyTwoCB_257459 : Nat.Prime 257459 := by norm_num

private theorem prime_eightyTwoCB_345263 : Nat.Prime 345263 := by norm_num

private theorem prime_eightyTwoCB_368111 : Nat.Prime 368111 := by norm_num

private theorem prime_eightyTwoCB_374359 : Nat.Prime 374359 := by norm_num

private theorem prime_eightyTwoCB_398477 : Nat.Prime 398477 := by norm_num

private theorem prime_eightyTwoCB_502669 : Nat.Prime 502669 := by norm_num

private theorem prime_eightyTwoCB_519229 : Nat.Prime 519229 := by norm_num

private theorem prime_eightyTwoCB_520853 : Nat.Prime 520853 := by norm_num

private theorem prime_eightyTwoCB_535793 : Nat.Prime 535793 := by norm_num

private theorem prime_eightyTwoCB_545449 : Nat.Prime 545449 := by norm_num

private theorem prime_eightyTwoCB_556723 : Nat.Prime 556723 := by norm_num

private theorem prime_eightyTwoCB_574543 : Nat.Prime 574543 := by norm_num

private theorem prime_eightyTwoCB_581953 : Nat.Prime 581953 := by norm_num

private theorem prime_eightyTwoCB_613229 : Nat.Prime 613229 := by norm_num

private theorem prime_eightyTwoCB_706019 : Nat.Prime 706019 := by norm_num

private theorem prime_eightyTwoCB_711817 : Nat.Prime 711817 := by norm_num

private theorem prime_eightyTwoCB_714869 : Nat.Prime 714869 := by norm_num

private theorem prime_eightyTwoCB_720779 : Nat.Prime 720779 := by norm_num

private theorem prime_eightyTwoCB_739253 : Nat.Prime 739253 := by norm_num

private theorem prime_eightyTwoCB_745837 : Nat.Prime 745837 := by norm_num

private theorem prime_eightyTwoCB_754381 : Nat.Prime 754381 := by norm_num

private theorem prime_eightyTwoCB_757109 : Nat.Prime 757109 := by norm_num

private theorem prime_eightyTwoCB_779189 : Nat.Prime 779189 := by norm_num

private theorem prime_eightyTwoCB_785809 : Nat.Prime 785809 := by norm_num

private theorem prime_eightyTwoCB_847787 : Nat.Prime 847787 := by norm_num

private theorem prime_eightyTwoCB_847967 : Nat.Prime 847967 := by norm_num

private theorem prime_eightyTwoCB_862957 : Nat.Prime 862957 := by norm_num

private theorem prime_eightyTwoCB_872203 : Nat.Prime 872203 := by norm_num

private theorem prime_eightyTwoCB_880981 : Nat.Prime 880981 := by norm_num

private theorem prime_eightyTwoCB_902179 : Nat.Prime 902179 := by norm_num

private theorem prime_eightyTwoCB_934891 : Nat.Prime 934891 := by norm_num

private theorem prime_eightyTwoCB_940327 : Nat.Prime 940327 := by norm_num

private theorem prime_eightyTwoCB_1030847 : Nat.Prime 1030847 := by norm_num

private theorem prime_eightyTwoCB_1046519 : Nat.Prime 1046519 := by norm_num

private theorem prime_eightyTwoCB_1054813 : Nat.Prime 1054813 := by norm_num

private theorem prime_eightyTwoCB_1140569 : Nat.Prime 1140569 := by norm_num

private theorem prime_eightyTwoCB_1220833 : Nat.Prime 1220833 := by norm_num

private theorem prime_eightyTwoCB_1303807 : Nat.Prime 1303807 := by norm_num

private theorem prime_eightyTwoCB_1410397 : Nat.Prime 1410397 := by norm_num

private theorem prime_eightyTwoCB_1457683 : Nat.Prime 1457683 := by norm_num

private theorem prime_eightyTwoCB_1504037 : Nat.Prime 1504037 := by norm_num

private theorem prime_eightyTwoCB_1513417 : Nat.Prime 1513417 := by norm_num

private theorem prime_eightyTwoCB_1557131 : Nat.Prime 1557131 := by norm_num

private theorem prime_eightyTwoCB_1559731 : Nat.Prime 1559731 := by norm_num

private theorem prime_eightyTwoCB_1679521 : Nat.Prime 1679521 := by norm_num

private theorem prime_eightyTwoCB_1691141 : Nat.Prime 1691141 := by norm_num

private theorem prime_eightyTwoCB_1782839 : Nat.Prime 1782839 := by norm_num

private theorem prime_eightyTwoCB_1863893 : Nat.Prime 1863893 := by norm_num

private theorem prime_eightyTwoCB_1874819 : Nat.Prime 1874819 := by norm_num

private theorem prime_eightyTwoCB_1950989 : Nat.Prime 1950989 := by norm_num

private theorem prime_eightyTwoCB_1954187 : Nat.Prime 1954187 := by norm_num

private theorem prime_eightyTwoCB_2058919 : Nat.Prime 2058919 := by norm_num

private theorem prime_eightyTwoCB_2220419 : Nat.Prime 2220419 := by norm_num

private theorem prime_eightyTwoCB_2242363 : Nat.Prime 2242363 := by norm_num

private theorem prime_eightyTwoCB_2279749 : Nat.Prime 2279749 := by norm_num

private theorem prime_eightyTwoCB_2283907 : Nat.Prime 2283907 := by norm_num

private theorem prime_eightyTwoCB_2407703 : Nat.Prime 2407703 := by norm_num

private theorem prime_eightyTwoCB_2417279 : Nat.Prime 2417279 := by norm_num

private theorem prime_eightyTwoCB_2550407 : Nat.Prime 2550407 := by norm_num

private theorem prime_eightyTwoCB_2628089 : Nat.Prime 2628089 := by norm_num

private theorem prime_eightyTwoCB_2639477 : Nat.Prime 2639477 := by norm_num

private theorem prime_eightyTwoCB_2662813 : Nat.Prime 2662813 := by norm_num

private theorem prime_eightyTwoCB_2685509 : Nat.Prime 2685509 := by norm_num

private theorem prime_eightyTwoCB_2774257 : Nat.Prime 2774257 := by norm_num

private theorem prime_eightyTwoCB_2800823 : Nat.Prime 2800823 := by norm_num

private theorem prime_eightyTwoCB_2847323 : Nat.Prime 2847323 := by norm_num

private theorem prime_eightyTwoCB_3097487 : Nat.Prime 3097487 := by norm_num

private theorem prime_eightyTwoCB_3109259 : Nat.Prime 3109259 := by norm_num

private theorem prime_eightyTwoCB_3111419 : Nat.Prime 3111419 := by norm_num

private theorem prime_eightyTwoCB_3127781 : Nat.Prime 3127781 := by norm_num

private theorem prime_eightyTwoCB_3131477 : Nat.Prime 3131477 := by norm_num

private theorem prime_eightyTwoCB_3362633 : Nat.Prime 3362633 := by norm_num

private theorem prime_eightyTwoCB_3450427 : Nat.Prime 3450427 := by norm_num

private theorem prime_eightyTwoCB_3475141 : Nat.Prime 3475141 := by norm_num

private theorem prime_eightyTwoCB_3727751 : Nat.Prime 3727751 := by norm_num

private theorem prime_eightyTwoCB_3737953 : Nat.Prime 3737953 := by norm_num

private theorem prime_eightyTwoCB_3840601 : Nat.Prime 3840601 := by norm_num

private theorem prime_eightyTwoCB_3931439 : Nat.Prime 3931439 := by norm_num

private theorem prime_eightyTwoCB_3993959 : Nat.Prime 3993959 := by norm_num

private theorem prime_eightyTwoCB_4058111 : Nat.Prime 4058111 := by norm_num

private theorem prime_eightyTwoCB_4207433 : Nat.Prime 4207433 := by norm_num

private theorem prime_eightyTwoCB_4796843 : Nat.Prime 4796843 := by norm_num

private theorem prime_eightyTwoCB_4819069 : Nat.Prime 4819069 := by norm_num

private theorem prime_eightyTwoCB_4923143 : Nat.Prime 4923143 := by norm_num

private theorem prime_eightyTwoCB_5227301 : Nat.Prime 5227301 := by norm_num

private theorem prime_eightyTwoCB_5312473 : Nat.Prime 5312473 := by norm_num

private theorem prime_eightyTwoCB_5410919 : Nat.Prime 5410919 := by norm_num

private theorem prime_eightyTwoCB_5949247 : Nat.Prime 5949247 := by norm_num

private theorem prime_eightyTwoCB_6056959 : Nat.Prime 6056959 := by norm_num

private theorem prime_eightyTwoCB_6789941 : Nat.Prime 6789941 := by norm_num

private theorem prime_eightyTwoCB_6915043 : Nat.Prime 6915043 := by norm_num

private theorem prime_eightyTwoCB_6961739 : Nat.Prime 6961739 := by norm_num

private theorem prime_eightyTwoCB_7084697 : Nat.Prime 7084697 := by norm_num

private theorem prime_eightyTwoCB_7663823 : Nat.Prime 7663823 := by norm_num

private theorem prime_eightyTwoCB_7682239 : Nat.Prime 7682239 := by norm_num

private theorem prime_eightyTwoCB_7955417 : Nat.Prime 7955417 := by norm_num

private theorem prime_eightyTwoCB_7994489 : Nat.Prime 7994489 := by norm_num

private theorem prime_eightyTwoCB_8073817 : Nat.Prime 8073817 := by norm_num

private theorem prime_eightyTwoCB_8911667 : Nat.Prime 8911667 := by norm_num

private theorem prime_eightyTwoCB_9318511 : Nat.Prime 9318511 := by norm_num

private theorem prime_eightyTwoCB_9359279 : Nat.Prime 9359279 := by norm_num

private theorem prime_eightyTwoCB_9397561 : Nat.Prime 9397561 := by norm_num

private theorem prime_eightyTwoCB_9922247 : Nat.Prime 9922247 := by norm_num

private theorem prime_eightyTwoCB_11864581 : Nat.Prime 11864581 := by norm_num

private theorem prime_eightyTwoCB_11953757 : Nat.Prime 11953757 := by norm_num

private theorem prime_eightyTwoCB_12892093 : Nat.Prime 12892093 := by norm_num

private theorem prime_eightyTwoCB_12930571 : Nat.Prime 12930571 := by norm_num

private theorem prime_eightyTwoCB_16050719 : Nat.Prime 16050719 := by norm_num

private theorem prime_eightyTwoCB_17725049 : Nat.Prime 17725049 := by norm_num

private theorem prime_eightyTwoCB_21641311 : Nat.Prime 21641311 := by norm_num

private theorem prime_eightyTwoCB_21788881 : Nat.Prime 21788881 := by norm_num

private theorem prime_eightyTwoCB_27661411 : Nat.Prime 27661411 := by norm_num

private theorem prime_eightyTwoCB_29514361 : Nat.Prime 29514361 := by norm_num

private theorem prime_eightyTwoCB_29994539 : Nat.Prime 29994539 := by norm_num

private theorem prime_eightyTwoCB_31395571 : Nat.Prime 31395571 := by
  apply lucas_primality 31395571 (7 : ZMod 31395571)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1046519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1046519, 1)] : List FactorBlock).map factorBlockValue).prod) = 31395571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1046519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31395571) ^ 15697785 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31395571) ^ 10465190 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31395571) ^ 6279114 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31395571) ^ 30 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_34050019 : Nat.Prime 34050019 := by
  apply lucas_primality 34050019 (2 : ZMod 34050019)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) = 34050019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_313
      · exact prime_eightyTwoCB_18131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34050019) ^ 17025009 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 34050019) ^ 11350006 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 34050019) ^ 108786 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 34050019) ^ 1878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_35653819 : Nat.Prime 35653819 := by
  apply lucas_primality 35653819 (2 : ZMod 35653819)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (59, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (59, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 35653819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35653819) ^ 17826909 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35653819) ^ 11884606 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35653819) ^ 1550166 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35653819) ^ 1229442 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35653819) ^ 604302 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35653819) ^ 236118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_39697561 : Nat.Prime 39697561 := by
  apply lucas_primality 39697561 (26 : ZMod 39697561)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (59, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (59, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 39697561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 39697561) ^ 19848780 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (26 : ZMod 39697561) ^ 13232520 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (26 : ZMod 39697561) ^ 7939512 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (26 : ZMod 39697561) ^ 5671080 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (26 : ZMod 39697561) ^ 672840 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (26 : ZMod 39697561) ^ 446040 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_40275199 : Nat.Prime 40275199 := by
  apply lucas_primality 40275199 (3 : ZMod 40275199)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (745837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (745837, 1)] : List FactorBlock).map factorBlockValue).prod) = 40275199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_745837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 40275199) ^ 20137599 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40275199) ^ 13425066 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 40275199) ^ 54 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_42152917 : Nat.Prime 42152917 := by
  apply lucas_primality 42152917 (14 : ZMod 42152917)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (37, 1), (67, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (37, 1), (67, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 42152917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 42152917) ^ 21076458 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (14 : ZMod 42152917) ^ 14050972 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (14 : ZMod 42152917) ^ 3242532 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (14 : ZMod 42152917) ^ 1139268 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (14 : ZMod 42152917) ^ 629148 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (14 : ZMod 42152917) ^ 386724 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_43330151 : Nat.Prime 43330151 := by
  apply lucas_primality 43330151 (7 : ZMod 43330151)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (83, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (83, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 43330151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_53
      · exact prime_eightyTwoCB_83
      · exact prime_eightyTwoCB_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 43330151) ^ 21665075 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 43330151) ^ 8666030 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 43330151) ^ 817550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 43330151) ^ 522050 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 43330151) ^ 219950 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_48442903 : Nat.Prime 48442903 := by
  apply lucas_primality 48442903 (3 : ZMod 48442903)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8073817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8073817, 1)] : List FactorBlock).map factorBlockValue).prod) = 48442903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_8073817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48442903) ^ 24221451 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48442903) ^ 16147634 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 48442903) ^ 6 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_52250941 : Nat.Prime 52250941 := by
  apply lucas_primality 52250941 (11 : ZMod 52250941)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (23, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (23, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) = 52250941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 52250941) ^ 26125470 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 52250941) ^ 17416980 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 52250941) ^ 10450188 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 52250941) ^ 7464420 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 52250941) ^ 2271780 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 52250941) ^ 86940 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_55128859 : Nat.Prime 55128859 := by
  apply lucas_primality 55128859 (2 : ZMod 55128859)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (113, 1), (4783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (113, 1), (4783, 1)] : List FactorBlock).map factorBlockValue).prod) = 55128859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_113
      · exact prime_eightyTwoCB_4783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55128859) ^ 27564429 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55128859) ^ 18376286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55128859) ^ 3242874 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55128859) ^ 487866 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55128859) ^ 11526 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_60611401 : Nat.Prime 60611401 := by
  apply lucas_primality 60611401 (23 : ZMod 60611401)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (151, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (151, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 60611401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_151
      · exact prime_eightyTwoCB_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 60611401) ^ 30305700 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (23 : ZMod 60611401) ^ 20203800 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (23 : ZMod 60611401) ^ 12122280 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (23 : ZMod 60611401) ^ 401400 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (23 : ZMod 60611401) ^ 271800 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_62295421 : Nat.Prime 62295421 := by
  apply lucas_primality 62295421 (7 : ZMod 62295421)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (37, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (37, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 62295421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62295421) ^ 31147710 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62295421) ^ 20765140 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62295421) ^ 12459084 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62295421) ^ 5663220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62295421) ^ 1683660 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62295421) ^ 24420 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_71722543 : Nat.Prime 71722543 := by
  apply lucas_primality 71722543 (3 : ZMod 71722543)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11953757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11953757, 1)] : List FactorBlock).map factorBlockValue).prod) = 71722543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11953757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71722543) ^ 35861271 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 71722543) ^ 23907514 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 71722543) ^ 6 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_78297061 : Nat.Prime 78297061 := by
  apply lucas_primality 78297061 (2 : ZMod 78297061)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (56737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (56737, 1)] : List FactorBlock).map factorBlockValue).prod) = 78297061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_56737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78297061) ^ 39148530 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78297061) ^ 26099020 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78297061) ^ 15659412 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78297061) ^ 3404220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78297061) ^ 1380 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_79013863 : Nat.Prime 79013863 := by
  apply lucas_primality 79013863 (3 : ZMod 79013863)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (59, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (59, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 79013863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_47
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 79013863) ^ 39506931 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79013863) ^ 26337954 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79013863) ^ 1681146 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79013863) ^ 1339218 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79013863) ^ 49914 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_79020517 : Nat.Prime 79020517 := by
  apply lucas_primality 79020517 (2 : ZMod 79020517)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (29009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (29009, 1)] : List FactorBlock).map factorBlockValue).prod) = 79020517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_227
      · exact prime_eightyTwoCB_29009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79020517) ^ 39510258 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79020517) ^ 26340172 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79020517) ^ 348108 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79020517) ^ 2724 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_79361641 : Nat.Prime 79361641 := by
  apply lucas_primality 79361641 (11 : ZMod 79361641)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (73483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (73483, 1)] : List FactorBlock).map factorBlockValue).prod) = 79361641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_73483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 79361641) ^ 39680820 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 79361641) ^ 26453880 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 79361641) ^ 15872328 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 79361641) ^ 1080 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_79879181 : Nat.Prime 79879181 := by
  apply lucas_primality 79879181 (3 : ZMod 79879181)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3993959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3993959, 1)] : List FactorBlock).map factorBlockValue).prod) = 79879181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_3993959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 79879181) ^ 39939590 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79879181) ^ 15975836 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 79879181) ^ 20 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_84148661 : Nat.Prime 84148661 := by
  apply lucas_primality 84148661 (2 : ZMod 84148661)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4207433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4207433, 1)] : List FactorBlock).map factorBlockValue).prod) = 84148661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_4207433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84148661) ^ 42074330 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 84148661) ^ 16829732 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 84148661) ^ 20 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_85113533 : Nat.Prime 85113533 := by
  apply lucas_primality 85113533 (2 : ZMod 85113533)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1109, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1109, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 85113533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_1109
      · exact prime_eightyTwoCB_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85113533) ^ 42556766 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85113533) ^ 12159076 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85113533) ^ 76748 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 85113533) ^ 31052 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_85898929 : Nat.Prime 85898929 := by
  apply lucas_primality 85898929 (22 : ZMod 85898929)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (29, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (29, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod) = 85898929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_2683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 85898929) ^ 42949464 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 85898929) ^ 28632976 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 85898929) ^ 3734736 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 85898929) ^ 2962032 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 85898929) ^ 32016 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_106182103 : Nat.Prime 106182103 := by
  apply lucas_primality 106182103 (5 : ZMod 106182103)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (80077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (80077, 1)] : List FactorBlock).map factorBlockValue).prod) = 106182103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_80077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 106182103) ^ 53091051 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106182103) ^ 35394034 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106182103) ^ 8167854 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106182103) ^ 6246006 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106182103) ^ 1326 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_108873431 : Nat.Prime 108873431 := by
  apply lucas_primality 108873431 (19 : ZMod 108873431)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1409, 1), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1409, 1), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) = 108873431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1409
      · exact prime_eightyTwoCB_7727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 108873431) ^ 54436715 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 108873431) ^ 21774686 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 108873431) ^ 77270 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 108873431) ^ 14090 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_110310721 : Nat.Prime 110310721 := by
  apply lucas_primality 110310721 (7 : ZMod 110310721)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (13, 1), (8839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (13, 1), (8839, 1)] : List FactorBlock).map factorBlockValue).prod) = 110310721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_8839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 110310721) ^ 55155360 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 110310721) ^ 36770240 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 110310721) ^ 22062144 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 110310721) ^ 8485440 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 110310721) ^ 12480 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_112866067 : Nat.Prime 112866067 := by
  apply lucas_primality 112866067 (2 : ZMod 112866067)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (919, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (919, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) = 112866067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_919
      · exact prime_eightyTwoCB_6823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112866067) ^ 56433033 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112866067) ^ 37622022 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112866067) ^ 122814 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 112866067) ^ 16542 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_117943171 : Nat.Prime 117943171 := by
  apply lucas_primality 117943171 (10 : ZMod 117943171)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3931439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3931439, 1)] : List FactorBlock).map factorBlockValue).prod) = 117943171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_3931439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 117943171) ^ 58971585 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 117943171) ^ 39314390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 117943171) ^ 23588634 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 117943171) ^ 30 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_123016939 : Nat.Prime 123016939 := by
  apply lucas_primality 123016939 (3 : ZMod 123016939)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1863893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1863893, 1)] : List FactorBlock).map factorBlockValue).prod) = 123016939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_1863893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 123016939) ^ 61508469 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 123016939) ^ 41005646 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 123016939) ^ 11183358 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 123016939) ^ 66 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_136878659 : Nat.Prime 136878659 := by
  apply lucas_primality 136878659 (2 : ZMod 136878659)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (60727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (60727, 1)] : List FactorBlock).map factorBlockValue).prod) = 136878659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_60727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 136878659) ^ 68439329 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136878659) ^ 19554094 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136878659) ^ 5951246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 136878659) ^ 2254 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_139506611 : Nat.Prime 139506611 := by
  apply lucas_primality 139506611 (2 : ZMod 139506611)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (156749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (156749, 1)] : List FactorBlock).map factorBlockValue).prod) = 139506611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_89
      · exact prime_eightyTwoCB_156749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139506611) ^ 69753305 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139506611) ^ 27901322 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139506611) ^ 1567490 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 139506611) ^ 890 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_149096177 : Nat.Prime 149096177 := by
  apply lucas_primality 149096177 (3 : ZMod 149096177)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (9318511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (9318511, 1)] : List FactorBlock).map factorBlockValue).prod) = 149096177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_9318511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 149096177) ^ 74548088 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 149096177) ^ 16 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_162073411 : Nat.Prime 162073411 := by
  apply lucas_primality 162073411 (2 : ZMod 162073411)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (23, 1), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (23, 1), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 162073411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 162073411) ^ 81036705 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 54024470 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 32414682 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 9533730 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 7046670 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 3953010 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 162073411) ^ 480930 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_166578917 : Nat.Prime 166578917 := by
  apply lucas_primality 166578917 (2 : ZMod 166578917)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (5949247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (5949247, 1)] : List FactorBlock).map factorBlockValue).prod) = 166578917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_5949247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 166578917) ^ 83289458 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 166578917) ^ 23796988 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 166578917) ^ 28 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_168611669 : Nat.Prime 168611669 := by
  apply lucas_primality 168611669 (2 : ZMod 168611669)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (42152917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (42152917, 1)] : List FactorBlock).map factorBlockValue).prod) = 168611669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_42152917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 168611669) ^ 84305834 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 168611669) ^ 4 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_172435831 : Nat.Prime 172435831 := by
  apply lucas_primality 172435831 (6 : ZMod 172435831)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (23, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (23, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) = 172435831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_1879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 172435831) ^ 86217915 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 57478610 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 34487166 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 24633690 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 9075570 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 7497210 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 172435831) ^ 91770 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_175745659 : Nat.Prime 175745659 := by
  apply lucas_primality 175745659 (2 : ZMod 175745659)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2662813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2662813, 1)] : List FactorBlock).map factorBlockValue).prod) = 175745659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_2662813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 175745659) ^ 87872829 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 175745659) ^ 58581886 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 175745659) ^ 15976878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 175745659) ^ 66 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_200858279 : Nat.Prime 200858279 := by
  apply lucas_primality 200858279 (13 : ZMod 200858279)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (839, 1), (119701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (839, 1), (119701, 1)] : List FactorBlock).map factorBlockValue).prod) = 200858279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_839
      · exact prime_eightyTwoCB_119701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 200858279) ^ 100429139 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 200858279) ^ 239402 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 200858279) ^ 1678 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_218635733 : Nat.Prime 218635733 := by
  apply lucas_primality 218635733 (2 : ZMod 218635733)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (167, 1), (46757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (167, 1), (46757, 1)] : List FactorBlock).map factorBlockValue).prod) = 218635733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_167
      · exact prime_eightyTwoCB_46757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 218635733) ^ 109317866 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 218635733) ^ 31233676 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 218635733) ^ 1309196 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 218635733) ^ 4676 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_221249939 : Nat.Prime 221249939 := by
  apply lucas_primality 221249939 (2 : ZMod 221249939)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (571, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (571, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) = 221249939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_571
      · exact prime_eightyTwoCB_2129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221249939) ^ 110624969 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249939) ^ 31607134 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249939) ^ 17019226 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249939) ^ 387478 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 221249939) ^ 103922 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_228283507 : Nat.Prime 228283507 := by
  apply lucas_primality 228283507 (5 : ZMod 228283507)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1051, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1051, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 228283507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_1051
      · exact prime_eightyTwoCB_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 228283507) ^ 114141753 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 228283507) ^ 76094502 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 228283507) ^ 20753046 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 228283507) ^ 217206 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 228283507) ^ 208098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_243480733 : Nat.Prime 243480733 := by
  apply lucas_primality 243480733 (5 : ZMod 243480733)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (108503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (108503, 1)] : List FactorBlock).map factorBlockValue).prod) = 243480733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_108503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 243480733) ^ 121740366 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 243480733) ^ 81160244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 243480733) ^ 22134612 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 243480733) ^ 14322396 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 243480733) ^ 2244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_244562161 : Nat.Prime 244562161 := by
  apply lucas_primality 244562161 (11 : ZMod 244562161)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (139, 1), (7331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (139, 1), (7331, 1)] : List FactorBlock).map factorBlockValue).prod) = 244562161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_139
      · exact prime_eightyTwoCB_7331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 244562161) ^ 122281080 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 244562161) ^ 81520720 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 244562161) ^ 48912432 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 244562161) ^ 1759440 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 244562161) ^ 33360 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_248224583 : Nat.Prime 248224583 := by
  apply lucas_primality 248224583 (5 : ZMod 248224583)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2693, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2693, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) = 248224583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_2693
      · exact prime_eightyTwoCB_2711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 248224583) ^ 124112291 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 248224583) ^ 14601446 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 248224583) ^ 92174 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 248224583) ^ 91562 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_253719413 : Nat.Prime 253719413 := by
  apply lucas_primality 253719413 (2 : ZMod 253719413)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1741, 1), (36433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1741, 1), (36433, 1)] : List FactorBlock).map factorBlockValue).prod) = 253719413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_1741
      · exact prime_eightyTwoCB_36433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 253719413) ^ 126859706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 253719413) ^ 145732 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 253719413) ^ 6964 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_262105469 : Nat.Prime 262105469 := by
  apply lucas_primality 262105469 (2 : ZMod 262105469)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (811, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (811, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) = 262105469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_811
      · exact prime_eightyTwoCB_1879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 262105469) ^ 131052734 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 262105469) ^ 6095476 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 262105469) ^ 323188 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 262105469) ^ 139492 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_280555003 : Nat.Prime 280555003 := by
  apply lucas_primality 280555003 (3 : ZMod 280555003)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (13, 1), (19031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (13, 1), (19031, 1)] : List FactorBlock).map factorBlockValue).prod) = 280555003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_19031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 280555003) ^ 140277501 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 280555003) ^ 93518334 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 280555003) ^ 40079286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 280555003) ^ 21581154 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 280555003) ^ 14742 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_286890173 : Nat.Prime 286890173 := by
  apply lucas_primality 286890173 (2 : ZMod 286890173)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71722543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71722543, 1)] : List FactorBlock).map factorBlockValue).prod) = 286890173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_71722543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 286890173) ^ 143445086 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 286890173) ^ 4 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_292183993 : Nat.Prime 292183993 := by
  apply lucas_primality 292183993 (5 : ZMod 292183993)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4058111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4058111, 1)] : List FactorBlock).map factorBlockValue).prod) = 292183993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_4058111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 292183993) ^ 146091996 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 292183993) ^ 97394664 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 292183993) ^ 72 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_300423553 : Nat.Prime 300423553 := by
  apply lucas_primality 300423553 (5 : ZMod 300423553)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (11, 1), (13, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (11, 1), (13, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) = 300423553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_5471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 300423553) ^ 150211776 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 300423553) ^ 100141184 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 300423553) ^ 27311232 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 300423553) ^ 23109504 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 300423553) ^ 54912 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_313472437 : Nat.Prime 313472437 := by
  apply lucas_primality 313472437 (2 : ZMod 313472437)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (706019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (706019, 1)] : List FactorBlock).map factorBlockValue).prod) = 313472437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_706019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 313472437) ^ 156736218 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 313472437) ^ 104490812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 313472437) ^ 8472228 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 313472437) ^ 444 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_348622097 : Nat.Prime 348622097 := by
  apply lucas_primality 348622097 (3 : ZMod 348622097)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (21788881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (21788881, 1)] : List FactorBlock).map factorBlockValue).prod) = 348622097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_21788881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 348622097) ^ 174311048 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 348622097) ^ 16 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_351664139 : Nat.Prime 351664139 := by
  apply lucas_primality 351664139 (6 : ZMod 351664139)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (263, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (263, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 351664139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_149
      · exact prime_eightyTwoCB_263
      · exact prime_eightyTwoCB_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 351664139) ^ 175832069 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 351664139) ^ 50237734 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 351664139) ^ 2360162 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 351664139) ^ 1337126 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 351664139) ^ 548618 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_363478783 : Nat.Prime 363478783 := by
  apply lucas_primality 363478783 (3 : ZMod 363478783)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1954187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1954187, 1)] : List FactorBlock).map factorBlockValue).prod) = 363478783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_1954187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 363478783) ^ 181739391 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 363478783) ^ 121159594 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 363478783) ^ 11725122 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 363478783) ^ 186 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_401716559 : Nat.Prime 401716559 := by
  apply lucas_primality 401716559 (17 : ZMod 401716559)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (200858279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (200858279, 1)] : List FactorBlock).map factorBlockValue).prod) = 401716559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_200858279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 401716559) ^ 200858279 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 401716559) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_436314379 : Nat.Prime 436314379 := by
  apply lucas_primality 436314379 (2 : ZMod 436314379)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1691141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1691141, 1)] : List FactorBlock).map factorBlockValue).prod) = 436314379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_1691141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 436314379) ^ 218157189 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 436314379) ^ 145438126 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 436314379) ^ 10146846 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 436314379) ^ 258 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_469171597 : Nat.Prime 469171597 := by
  apply lucas_primality 469171597 (2 : ZMod 469171597)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (233, 1), (167801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (233, 1), (167801, 1)] : List FactorBlock).map factorBlockValue).prod) = 469171597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_233
      · exact prime_eightyTwoCB_167801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 469171597) ^ 234585798 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 469171597) ^ 156390532 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 469171597) ^ 2013612 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 469171597) ^ 2796 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_496449167 : Nat.Prime 496449167 := by
  apply lucas_primality 496449167 (5 : ZMod 496449167)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (248224583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (248224583, 1)] : List FactorBlock).map factorBlockValue).prod) = 496449167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_248224583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 496449167) ^ 248224583 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 496449167) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_516019783 : Nat.Prime 516019783 := by
  apply lucas_primality 516019783 (3 : ZMod 516019783)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (1457683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (1457683, 1)] : List FactorBlock).map factorBlockValue).prod) = 516019783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_1457683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 516019783) ^ 258009891 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 516019783) ^ 172006594 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 516019783) ^ 8746098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 516019783) ^ 354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_649597679 : Nat.Prime 649597679 := by
  apply lucas_primality 649597679 (11 : ZMod 649597679)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1429, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1429, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) = 649597679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_1429
      · exact prime_eightyTwoCB_6143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 649597679) ^ 324798839 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 649597679) ^ 17556694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 649597679) ^ 454582 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 649597679) ^ 105746 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_699141559 : Nat.Prime 699141559 := by
  apply lucas_primality 699141559 (3 : ZMod 699141559)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (159403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (159403, 1)] : List FactorBlock).map factorBlockValue).prod) = 699141559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_159403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 699141559) ^ 349570779 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 699141559) ^ 233047186 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 699141559) ^ 41125974 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 699141559) ^ 16259106 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 699141559) ^ 4386 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_703081867 : Nat.Prime 703081867 := by
  apply lucas_primality 703081867 (2 : ZMod 703081867)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8171, 1), (14341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8171, 1), (14341, 1)] : List FactorBlock).map factorBlockValue).prod) = 703081867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_8171
      · exact prime_eightyTwoCB_14341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 703081867) ^ 351540933 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 703081867) ^ 234360622 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 703081867) ^ 86046 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 703081867) ^ 49026 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_773291221 : Nat.Prime 773291221 := by
  apply lucas_primality 773291221 (10 : ZMod 773291221)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (67, 1), (14797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (67, 1), (14797, 1)] : List FactorBlock).map factorBlockValue).prod) = 773291221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_14797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 773291221) ^ 386645610 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 773291221) ^ 257763740 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 773291221) ^ 154658244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 773291221) ^ 59483940 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 773291221) ^ 11541660 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 773291221) ^ 52260 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_894577063 : Nat.Prime 894577063 := by
  apply lucas_primality 894577063 (3 : ZMod 894577063)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149096177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149096177, 1)] : List FactorBlock).map factorBlockValue).prod) = 894577063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_149096177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 894577063) ^ 447288531 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 894577063) ^ 298192354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 894577063) ^ 6 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_920687951 : Nat.Prime 920687951 := by
  apply lucas_primality 920687951 (7 : ZMod 920687951)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (13, 1), (137, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (13, 1), (137, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 920687951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_137
      · exact prime_eightyTwoCB_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 920687951) ^ 460343975 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 920687951) ^ 184137590 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 920687951) ^ 131526850 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 920687951) ^ 70822150 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 920687951) ^ 6720350 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 920687951) ^ 4363450 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_979326091 : Nat.Prime 979326091 := by
  apply lucas_primality 979326091 (10 : ZMod 979326091)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (619, 1), (17579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (619, 1), (17579, 1)] : List FactorBlock).map factorBlockValue).prod) = 979326091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_619
      · exact prime_eightyTwoCB_17579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 979326091) ^ 489663045 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 979326091) ^ 326442030 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 979326091) ^ 195865218 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 979326091) ^ 1582110 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 979326091) ^ 55710 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_991647913 : Nat.Prime 991647913 := by
  apply lucas_primality 991647913 (5 : ZMod 991647913)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (581953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (581953, 1)] : List FactorBlock).map factorBlockValue).prod) = 991647913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_71
      · exact prime_eightyTwoCB_581953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 991647913) ^ 495823956 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 991647913) ^ 330549304 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 991647913) ^ 13966872 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 991647913) ^ 1704 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1061821031 : Nat.Prime 1061821031 := by
  apply lucas_primality 1061821031 (17 : ZMod 1061821031)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (106182103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (106182103, 1)] : List FactorBlock).map factorBlockValue).prod) = 1061821031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_106182103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 1061821031) ^ 530910515 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 1061821031) ^ 212364206 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 1061821031) ^ 10 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1089550321 : Nat.Prime 1089550321 := by
  apply lucas_primality 1089550321 (13 : ZMod 1089550321)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (881, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (881, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1089550321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_881
      · exact prime_eightyTwoCB_5153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1089550321) ^ 544775160 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1089550321) ^ 363183440 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1089550321) ^ 217910064 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1089550321) ^ 1236720 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1089550321) ^ 211440 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1099954763 : Nat.Prime 1099954763 := by
  apply lucas_primality 1099954763 (2 : ZMod 1099954763)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (6961739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (6961739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1099954763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_79
      · exact prime_eightyTwoCB_6961739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1099954763) ^ 549977381 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1099954763) ^ 13923478 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1099954763) ^ 158 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1103107211 : Nat.Prime 1103107211 := by
  apply lucas_primality 1103107211 (2 : ZMod 1103107211)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (110310721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (110310721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103107211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_110310721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1103107211) ^ 551553605 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103107211) ^ 220621442 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103107211) ^ 10 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1329782213 : Nat.Prime 1329782213 := by
  apply lucas_primality 1329782213 (2 : ZMod 1329782213)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (733, 1), (41231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (733, 1), (41231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1329782213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_733
      · exact prime_eightyTwoCB_41231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1329782213) ^ 664891106 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329782213) ^ 120889292 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329782213) ^ 1814164 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329782213) ^ 32252 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1362594839 : Nat.Prime 1362594839 := by
  apply lucas_primality 1362594839 (7 : ZMod 1362594839)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (101, 1), (613229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (101, 1), (613229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362594839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_101
      · exact prime_eightyTwoCB_613229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1362594839) ^ 681297419 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1362594839) ^ 123872258 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1362594839) ^ 13491038 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1362594839) ^ 2222 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1383053249 : Nat.Prime 1383053249 := by
  apply lucas_primality 1383053249 (3 : ZMod 1383053249)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (317, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (317, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1383053249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_317
      · exact prime_eightyTwoCB_68171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1383053249) ^ 691526624 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383053249) ^ 4362944 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383053249) ^ 20288 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1880834623 : Nat.Prime 1880834623 := by
  apply lucas_primality 1880834623 (3 : ZMod 1880834623)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313472437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313472437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880834623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_313472437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1880834623) ^ 940417311 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1880834623) ^ 626944874 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1880834623) ^ 6 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1916301227 : Nat.Prime 1916301227 := by
  apply lucas_primality 1916301227 (11 : ZMod 1916301227)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (136878659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (136878659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1916301227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_136878659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1916301227) ^ 958150613 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1916301227) ^ 273757318 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1916301227) ^ 14 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2067700573 : Nat.Prime 2067700573 := by
  apply lucas_primality 2067700573 (5 : ZMod 2067700573)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (2333, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (2333, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2067700573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_2333
      · exact prime_eightyTwoCB_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2067700573) ^ 1033850286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2067700573) ^ 689233524 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2067700573) ^ 295385796 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2067700573) ^ 886284 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2067700573) ^ 587916 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2396375431 : Nat.Prime 2396375431 := by
  apply lucas_primality 2396375431 (3 : ZMod 2396375431)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79879181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79879181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2396375431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_79879181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2396375431) ^ 1198187715 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2396375431) ^ 798791810 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2396375431) ^ 479275086 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2396375431) ^ 30 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2420177603 : Nat.Prime 2420177603 := by
  apply lucas_primality 2420177603 (2 : ZMod 2420177603)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (29514361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (29514361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2420177603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_29514361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2420177603) ^ 1210088801 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420177603) ^ 59028722 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2420177603) ^ 82 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2615916763 : Nat.Prime 2615916763 := by
  apply lucas_primality 2615916763 (2 : ZMod 2615916763)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (48442903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (48442903, 1)] : List FactorBlock).map factorBlockValue).prod) = 2615916763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_48442903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2615916763) ^ 1307958381 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2615916763) ^ 871972254 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2615916763) ^ 54 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2686471343 : Nat.Prime 2686471343 := by
  apply lucas_primality 2686471343 (5 : ZMod 2686471343)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (79013863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (79013863, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686471343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_79013863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2686471343) ^ 1343235671 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686471343) ^ 158027726 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686471343) ^ 34 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2796566237 : Nat.Prime 2796566237 := by
  apply lucas_primality 2796566237 (2 : ZMod 2796566237)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (699141559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (699141559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2796566237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_699141559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2796566237) ^ 1398283118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2796566237) ^ 4 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3028109611 : Nat.Prime 3028109611 := by
  apply lucas_primality 3028109611 (2 : ZMod 3028109611)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (5312473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (5312473, 1)] : List FactorBlock).map factorBlockValue).prod) = 3028109611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_5312473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3028109611) ^ 1514054805 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3028109611) ^ 1009369870 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3028109611) ^ 605621922 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3028109611) ^ 159374190 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3028109611) ^ 570 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3097499147 : Nat.Prime 3097499147 := by
  apply lucas_primality 3097499147 (5 : ZMod 3097499147)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (221249939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (221249939, 1)] : List FactorBlock).map factorBlockValue).prod) = 3097499147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_221249939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3097499147) ^ 1548749573 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3097499147) ^ 442499878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3097499147) ^ 14 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3934089227 : Nat.Prime 3934089227 := by
  apply lucas_primality 3934089227 (2 : ZMod 3934089227)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (193, 1), (167081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (193, 1), (167081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3934089227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_61
      · exact prime_eightyTwoCB_193
      · exact prime_eightyTwoCB_167081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3934089227) ^ 1967044613 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3934089227) ^ 64493266 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3934089227) ^ 20383882 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3934089227) ^ 23546 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3971593337 : Nat.Prime 3971593337 := by
  apply lucas_primality 3971593337 (3 : ZMod 3971593337)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (496449167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (496449167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3971593337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_496449167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3971593337) ^ 1985796668 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3971593337) ^ 8 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_4176368741 : Nat.Prime 4176368741 := by
  apply lucas_primality 4176368741 (7 : ZMod 4176368741)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3407, 1), (61291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3407, 1), (61291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4176368741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_3407
      · exact prime_eightyTwoCB_61291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4176368741) ^ 2088184370 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4176368741) ^ 835273748 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4176368741) ^ 1225820 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4176368741) ^ 68140 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_5423396239 : Nat.Prime 5423396239 := by
  apply lucas_primality 5423396239 (6 : ZMod 5423396239)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (1782839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (1782839, 1)] : List FactorBlock).map factorBlockValue).prod) = 5423396239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_1782839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5423396239) ^ 2711698119 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5423396239) ^ 1807798746 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5423396239) ^ 417184326 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 5423396239) ^ 3042 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_5729860141 : Nat.Prime 5729860141 := by
  apply lucas_primality 5729860141 (7 : ZMod 5729860141)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1637, 1), (58337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1637, 1), (58337, 1)] : List FactorBlock).map factorBlockValue).prod) = 5729860141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1637
      · exact prime_eightyTwoCB_58337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5729860141) ^ 2864930070 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5729860141) ^ 1909953380 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5729860141) ^ 1145972028 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5729860141) ^ 3500220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 5729860141) ^ 98220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6203867587 : Nat.Prime 6203867587 := by
  apply lucas_primality 6203867587 (5 : ZMod 6203867587)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (199, 1), (727, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (199, 1), (727, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) = 6203867587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_199
      · exact prime_eightyTwoCB_727
      · exact prime_eightyTwoCB_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6203867587) ^ 3101933793 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203867587) ^ 2067955862 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203867587) ^ 886266798 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203867587) ^ 31175214 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203867587) ^ 8533518 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6203867587) ^ 6076266 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6329954503 : Nat.Prime 6329954503 := by
  apply lucas_primality 6329954503 (5 : ZMod 6329954503)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (351664139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (351664139, 1)] : List FactorBlock).map factorBlockValue).prod) = 6329954503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_351664139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6329954503) ^ 3164977251 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6329954503) ^ 2109984834 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6329954503) ^ 18 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6417620953 : Nat.Prime 6417620953 := by
  apply lucas_primality 6417620953 (5 : ZMod 6417620953)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7919, 1), (33767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7919, 1), (33767, 1)] : List FactorBlock).map factorBlockValue).prod) = 6417620953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7919
      · exact prime_eightyTwoCB_33767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6417620953) ^ 3208810476 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6417620953) ^ 2139206984 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6417620953) ^ 810408 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6417620953) ^ 190056 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6541163579 : Nat.Prime 6541163579 := by
  apply lucas_primality 6541163579 (2 : ZMod 6541163579)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (8911667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (8911667, 1)] : List FactorBlock).map factorBlockValue).prod) = 6541163579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_367
      · exact prime_eightyTwoCB_8911667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6541163579) ^ 3270581789 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6541163579) ^ 17823334 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6541163579) ^ 734 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7230898063 : Nat.Prime 7230898063 := by
  apply lucas_primality 7230898063 (5 : ZMod 7230898063)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (401716559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (401716559, 1)] : List FactorBlock).map factorBlockValue).prod) = 7230898063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_401716559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7230898063) ^ 3615449031 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 7230898063) ^ 2410299354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 7230898063) ^ 18 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7253058193 : Nat.Prime 7253058193 := by
  apply lucas_primality 7253058193 (29 : ZMod 7253058193)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11369, 1), (13291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11369, 1), (13291, 1)] : List FactorBlock).map factorBlockValue).prod) = 7253058193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11369
      · exact prime_eightyTwoCB_13291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 7253058193) ^ 3626529096 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (29 : ZMod 7253058193) ^ 2417686064 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (29 : ZMod 7253058193) ^ 637968 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (29 : ZMod 7253058193) ^ 545712 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7617589909 : Nat.Prime 7617589909 := by
  apply lucas_primality 7617589909 (2 : ZMod 7617589909)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (223, 1), (167449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (223, 1), (167449, 1)] : List FactorBlock).map factorBlockValue).prod) = 7617589909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_223
      · exact prime_eightyTwoCB_167449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7617589909) ^ 3808794954 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7617589909) ^ 2539196636 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7617589909) ^ 448093524 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7617589909) ^ 34159596 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7617589909) ^ 45492 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8767135961 : Nat.Prime 8767135961 := by
  apply lucas_primality 8767135961 (3 : ZMod 8767135961)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (17, 1), (109, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (17, 1), (109, 1), (10753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8767135961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_109
      · exact prime_eightyTwoCB_10753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8767135961) ^ 4383567980 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8767135961) ^ 1753427192 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8767135961) ^ 797012360 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8767135961) ^ 515713880 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8767135961) ^ 80432440 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8767135961) ^ 815320 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8960553599 : Nat.Prime 8960553599 := by
  apply lucas_primality 8960553599 (7 : ZMod 8960553599)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (263, 1), (165391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (263, 1), (165391, 1)] : List FactorBlock).map factorBlockValue).prod) = 8960553599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_103
      · exact prime_eightyTwoCB_263
      · exact prime_eightyTwoCB_165391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8960553599) ^ 4480276799 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8960553599) ^ 86995666 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8960553599) ^ 34070546 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8960553599) ^ 54178 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_9720414001 : Nat.Prime 9720414001 := by
  apply lucas_primality 9720414001 (62 : ZMod 9720414001)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 3), (11, 2), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 3), (11, 2), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 9720414001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (62 : ZMod 9720414001) ^ 4860207000 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (62 : ZMod 9720414001) ^ 3240138000 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (62 : ZMod 9720414001) ^ 1944082800 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (62 : ZMod 9720414001) ^ 883674000 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (62 : ZMod 9720414001) ^ 2178000 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_9973045963 : Nat.Prime 9973045963 := by
  apply lucas_primality 9973045963 (2 : ZMod 9973045963)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (23, 1), (151, 1), (14503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (23, 1), (151, 1), (14503, 1)] : List FactorBlock).map factorBlockValue).prod) = 9973045963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_151
      · exact prime_eightyTwoCB_14503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9973045963) ^ 4986522981 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9973045963) ^ 3324348654 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9973045963) ^ 906640542 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9973045963) ^ 433610694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9973045963) ^ 66046662 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9973045963) ^ 687654 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11453073257 : Nat.Prime 11453073257 := by
  apply lucas_primality 11453073257 (3 : ZMod 11453073257)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (569, 1), (81163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (569, 1), (81163, 1)] : List FactorBlock).map factorBlockValue).prod) = 11453073257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_569
      · exact prime_eightyTwoCB_81163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11453073257) ^ 5726536628 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11453073257) ^ 369453976 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11453073257) ^ 20128424 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 11453073257) ^ 141112 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11731166023 : Nat.Prime 11731166023 := by
  apply lucas_primality 11731166023 (5 : ZMod 11731166023)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (263, 1), (58537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (263, 1), (58537, 1)] : List FactorBlock).map factorBlockValue).prod) = 11731166023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_127
      · exact prime_eightyTwoCB_263
      · exact prime_eightyTwoCB_58537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11731166023) ^ 5865583011 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11731166023) ^ 3910388674 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11731166023) ^ 92371386 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11731166023) ^ 44605194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 11731166023) ^ 200406 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11791969171 : Nat.Prime 11791969171 := by
  apply lucas_primality 11791969171 (12 : ZMod 11791969171)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (101, 1), (63799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (101, 1), (63799, 1)] : List FactorBlock).map factorBlockValue).prod) = 11791969171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_61
      · exact prime_eightyTwoCB_101
      · exact prime_eightyTwoCB_63799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 11791969171) ^ 5895984585 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (12 : ZMod 11791969171) ^ 3930656390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (12 : ZMod 11791969171) ^ 2358393834 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (12 : ZMod 11791969171) ^ 193310970 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (12 : ZMod 11791969171) ^ 116752170 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (12 : ZMod 11791969171) ^ 184830 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_13710393731 : Nat.Prime 13710393731 := by
  apply lucas_primality 13710393731 (2 : ZMod 13710393731)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 2), (345263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 2), (345263, 1)] : List FactorBlock).map factorBlockValue).prod) = 13710393731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_345263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13710393731) ^ 6855196865 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13710393731) ^ 2742078746 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13710393731) ^ 1246399430 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13710393731) ^ 721599670 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13710393731) ^ 39710 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_14363491013 : Nat.Prime 14363491013 := by
  apply lucas_primality 14363491013 (2 : ZMod 14363491013)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (1103, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (1103, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) = 14363491013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_1103
      · exact prime_eightyTwoCB_14731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14363491013) ^ 7181745506 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14363491013) ^ 1104883924 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14363491013) ^ 844911236 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14363491013) ^ 13022204 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14363491013) ^ 975052 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_16710428797 : Nat.Prime 16710428797 := by
  apply lucas_primality 16710428797 (2 : ZMod 16710428797)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (191, 1), (199, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (191, 1), (199, 1), (36637, 1)] : List FactorBlock).map factorBlockValue).prod) = 16710428797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_191
      · exact prime_eightyTwoCB_199
      · exact prime_eightyTwoCB_36637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16710428797) ^ 8355214398 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16710428797) ^ 5570142932 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16710428797) ^ 87489156 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16710428797) ^ 83972004 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16710428797) ^ 456108 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_19969547341 : Nat.Prime 19969547341 := by
  apply lucas_primality 19969547341 (6 : ZMod 19969547341)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (641, 1), (519229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (641, 1), (519229, 1)] : List FactorBlock).map factorBlockValue).prod) = 19969547341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_641
      · exact prime_eightyTwoCB_519229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19969547341) ^ 9984773670 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 19969547341) ^ 6656515780 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 19969547341) ^ 3993909468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 19969547341) ^ 31153740 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 19969547341) ^ 38460 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_20273365109 : Nat.Prime 20273365109 := by
  apply lucas_primality 20273365109 (2 : ZMod 20273365109)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (52250941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (52250941, 1)] : List FactorBlock).map factorBlockValue).prod) = 20273365109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_97
      · exact prime_eightyTwoCB_52250941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20273365109) ^ 10136682554 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20273365109) ^ 209003764 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20273365109) ^ 388 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_22303808119 : Nat.Prime 22303808119 := by
  apply lucas_primality 22303808119 (3 : ZMod 22303808119)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (229, 1), (5410919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (229, 1), (5410919, 1)] : List FactorBlock).map factorBlockValue).prod) = 22303808119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_229
      · exact prime_eightyTwoCB_5410919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22303808119) ^ 11151904059 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22303808119) ^ 7434602706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22303808119) ^ 97396542 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22303808119) ^ 4122 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_23308392439 : Nat.Prime 23308392439 := by
  apply lucas_primality 23308392439 (6 : ZMod 23308392439)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (257, 1), (1679521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (257, 1), (1679521, 1)] : List FactorBlock).map factorBlockValue).prod) = 23308392439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_257
      · exact prime_eightyTwoCB_1679521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 23308392439) ^ 11654196219 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23308392439) ^ 7769464146 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23308392439) ^ 90694134 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 23308392439) ^ 13878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_23990159129 : Nat.Prime 23990159129 := by
  apply lucas_primality 23990159129 (3 : ZMod 23990159129)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (101, 1), (2283907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (101, 1), (2283907, 1)] : List FactorBlock).map factorBlockValue).prod) = 23990159129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_101
      · exact prime_eightyTwoCB_2283907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23990159129) ^ 11995079564 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23990159129) ^ 1845396856 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23990159129) ^ 237526328 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23990159129) ^ 10504 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_27420787463 : Nat.Prime 27420787463 := by
  apply lucas_primality 27420787463 (5 : ZMod 27420787463)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13710393731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13710393731, 1)] : List FactorBlock).map factorBlockValue).prod) = 27420787463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13710393731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 27420787463) ^ 13710393731 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 27420787463) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_28726982027 : Nat.Prime 28726982027 := by
  apply lucas_primality 28726982027 (2 : ZMod 28726982027)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14363491013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14363491013, 1)] : List FactorBlock).map factorBlockValue).prod) = 28726982027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_14363491013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28726982027) ^ 14363491013 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 28726982027) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_30562909337 : Nat.Prime 30562909337 := by
  apply lucas_primality 30562909337 (3 : ZMod 30562909337)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4903, 1), (779189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4903, 1), (779189, 1)] : List FactorBlock).map factorBlockValue).prod) = 30562909337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_4903
      · exact prime_eightyTwoCB_779189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30562909337) ^ 15281454668 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30562909337) ^ 6233512 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30562909337) ^ 39224 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_35000601107 : Nat.Prime 35000601107 := by
  apply lucas_primality 35000601107 (2 : ZMod 35000601107)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (286890173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (286890173, 1)] : List FactorBlock).map factorBlockValue).prod) = 35000601107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_61
      · exact prime_eightyTwoCB_286890173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35000601107) ^ 17500300553 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35000601107) ^ 573780346 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35000601107) ^ 122 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_37867657657 : Nat.Prime 37867657657 := by
  apply lucas_primality 37867657657 (13 : ZMod 37867657657)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (379, 1), (509, 1), (8179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (379, 1), (509, 1), (8179, 1)] : List FactorBlock).map factorBlockValue).prod) = 37867657657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_379
      · exact prime_eightyTwoCB_509
      · exact prime_eightyTwoCB_8179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 37867657657) ^ 18933828828 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 37867657657) ^ 12622552552 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 37867657657) ^ 99914664 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 37867657657) ^ 74396184 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 37867657657) ^ 4629864 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_40978413583 : Nat.Prime 40978413583 := by
  apply lucas_primality 40978413583 (5 : ZMod 40978413583)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (166578917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (166578917, 1)] : List FactorBlock).map factorBlockValue).prod) = 40978413583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_166578917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40978413583) ^ 20489206791 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40978413583) ^ 13659471194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40978413583) ^ 999473502 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 40978413583) ^ 246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_51990002371 : Nat.Prime 51990002371 := by
  apply lucas_primality 51990002371 (10 : ZMod 51990002371)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (739, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (739, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) = 51990002371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_89
      · exact prime_eightyTwoCB_739
      · exact prime_eightyTwoCB_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 51990002371) ^ 25995001185 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 51990002371) ^ 17330000790 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 51990002371) ^ 10398000474 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 51990002371) ^ 584157330 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 51990002371) ^ 70351830 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 51990002371) ^ 5919390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_57335962037 : Nat.Prime 57335962037 := by
  apply lucas_primality 57335962037 (2 : ZMod 57335962037)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (112866067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (112866067, 1)] : List FactorBlock).map factorBlockValue).prod) = 57335962037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_127
      · exact prime_eightyTwoCB_112866067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57335962037) ^ 28667981018 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57335962037) ^ 451464268 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 57335962037) ^ 508 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_60084199313 : Nat.Prime 60084199313 := by
  apply lucas_primality 60084199313 (3 : ZMod 60084199313)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2003, 1), (1874819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2003, 1), (1874819, 1)] : List FactorBlock).map factorBlockValue).prod) = 60084199313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_2003
      · exact prime_eightyTwoCB_1874819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60084199313) ^ 30042099656 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 60084199313) ^ 29997104 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 60084199313) ^ 32048 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_72971795359 : Nat.Prime 72971795359 := by
  apply lucas_primality 72971795359 (3 : ZMod 72971795359)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (67, 1), (785809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (67, 1), (785809, 1)] : List FactorBlock).map factorBlockValue).prod) = 72971795359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_785809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72971795359) ^ 36485897679 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 72971795359) ^ 24323931786 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 72971795359) ^ 10424542194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 72971795359) ^ 6633799578 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 72971795359) ^ 1089131274 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 72971795359) ^ 92862 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_79276471733 : Nat.Prime 79276471733 := by
  apply lucas_primality 79276471733 (2 : ZMod 79276471733)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6329, 1), (3131477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6329, 1), (3131477, 1)] : List FactorBlock).map factorBlockValue).prod) = 79276471733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_6329
      · exact prime_eightyTwoCB_3131477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79276471733) ^ 39638235866 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79276471733) ^ 12525908 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 79276471733) ^ 25316 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_86002554041 : Nat.Prime 86002554041 := by
  apply lucas_primality 86002554041 (3 : ZMod 86002554041)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (23, 1), (1511, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (23, 1), (1511, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) = 86002554041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_1511
      · exact prime_eightyTwoCB_4759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 86002554041) ^ 43001277020 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 86002554041) ^ 17200510808 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 86002554041) ^ 6615581080 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 86002554041) ^ 3739241480 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 86002554041) ^ 56917640 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 86002554041) ^ 18071560 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_101906281649 : Nat.Prime 101906281649 := by
  apply lucas_primality 101906281649 (3 : ZMod 101906281649)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (31, 1), (7084697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (31, 1), (7084697, 1)] : List FactorBlock).map factorBlockValue).prod) = 101906281649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_7084697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101906281649) ^ 50953140824 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 101906281649) ^ 3514009712 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 101906281649) ^ 3287299408 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 101906281649) ^ 14384 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_103192140713 : Nat.Prime 103192140713 := by
  apply lucas_primality 103192140713 (3 : ZMod 103192140713)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (348622097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (348622097, 1)] : List FactorBlock).map factorBlockValue).prod) = 103192140713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_348622097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103192140713) ^ 51596070356 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 103192140713) ^ 2788976776 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 103192140713) ^ 296 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_103407935867 : Nat.Prime 103407935867 := by
  apply lucas_primality 103407935867 (2 : ZMod 103407935867)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2917, 1), (17725049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2917, 1), (17725049, 1)] : List FactorBlock).map factorBlockValue).prod) = 103407935867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_2917
      · exact prime_eightyTwoCB_17725049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103407935867) ^ 51703967933 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 103407935867) ^ 35450098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 103407935867) ^ 5834 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_106371215707 : Nat.Prime 106371215707 := by
  apply lucas_primality 106371215707 (5 : ZMod 106371215707)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (373, 1), (6789941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (373, 1), (6789941, 1)] : List FactorBlock).map factorBlockValue).prod) = 106371215707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_373
      · exact prime_eightyTwoCB_6789941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 106371215707) ^ 53185607853 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106371215707) ^ 35457071902 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106371215707) ^ 15195887958 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106371215707) ^ 285177522 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 106371215707) ^ 15666 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_125908827053 : Nat.Prime 125908827053 := by
  apply lucas_primality 125908827053 (2 : ZMod 125908827053)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (516019783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (516019783, 1)] : List FactorBlock).map factorBlockValue).prod) = 125908827053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_61
      · exact prime_eightyTwoCB_516019783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 125908827053) ^ 62954413526 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 125908827053) ^ 2064079132 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 125908827053) ^ 244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_137671141549 : Nat.Prime 137671141549 := by
  apply lucas_primality 137671141549 (2 : ZMod 137671141549)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (39697561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (39697561, 1)] : List FactorBlock).map factorBlockValue).prod) = 137671141549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_39697561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 137671141549) ^ 68835570774 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 137671141549) ^ 45890380516 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 137671141549) ^ 8098302444 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 137671141549) ^ 3468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_154280681167 : Nat.Prime 154280681167 := by
  apply lucas_primality 154280681167 (3 : ZMod 154280681167)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (108799, 1), (236339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (108799, 1), (236339, 1)] : List FactorBlock).map factorBlockValue).prod) = 154280681167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_108799
      · exact prime_eightyTwoCB_236339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 154280681167) ^ 77140340583 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 154280681167) ^ 51426893722 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 154280681167) ^ 1418034 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 154280681167) ^ 652794 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_158552943467 : Nat.Prime 158552943467 := by
  apply lucas_primality 158552943467 (2 : ZMod 158552943467)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79276471733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79276471733, 1)] : List FactorBlock).map factorBlockValue).prod) = 158552943467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_79276471733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 158552943467) ^ 79276471733 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 158552943467) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_176399475509 : Nat.Prime 176399475509 := by
  apply lucas_primality 176399475509 (2 : ZMod 176399475509)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (269, 1), (1504037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (269, 1), (1504037, 1)] : List FactorBlock).map factorBlockValue).prod) = 176399475509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_109
      · exact prime_eightyTwoCB_269
      · exact prime_eightyTwoCB_1504037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 176399475509) ^ 88199737754 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176399475509) ^ 1618343812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176399475509) ^ 655760132 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 176399475509) ^ 117284 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_211828237711 : Nat.Prime 211828237711 := by
  apply lucas_primality 211828237711 (15 : ZMod 211828237711)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (243480733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (243480733, 1)] : List FactorBlock).map factorBlockValue).prod) = 211828237711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_243480733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 211828237711) ^ 105914118855 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (15 : ZMod 211828237711) ^ 70609412570 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (15 : ZMod 211828237711) ^ 42365647542 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (15 : ZMod 211828237711) ^ 7304421990 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (15 : ZMod 211828237711) ^ 870 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_223461601577 : Nat.Prime 223461601577 := by
  apply lucas_primality 223461601577 (3 : ZMod 223461601577)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (649597679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (649597679, 1)] : List FactorBlock).map factorBlockValue).prod) = 223461601577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_649597679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 223461601577) ^ 111730800788 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 223461601577) ^ 5196781432 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 223461601577) ^ 344 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_232709112113 : Nat.Prime 232709112113 := by
  apply lucas_primality 232709112113 (3 : ZMod 232709112113)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (469171597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (469171597, 1)] : List FactorBlock).map factorBlockValue).prod) = 232709112113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_469171597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 232709112113) ^ 116354556056 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 232709112113) ^ 7506745552 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 232709112113) ^ 496 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_250273149251 : Nat.Prime 250273149251 := by
  apply lucas_primality 250273149251 (2 : ZMod 250273149251)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (547, 1), (827, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (547, 1), (827, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) = 250273149251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_547
      · exact prime_eightyTwoCB_827
      · exact prime_eightyTwoCB_2213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 250273149251) ^ 125136574625 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 250273149251) ^ 50054629850 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 250273149251) ^ 457537750 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 250273149251) ^ 302627750 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 250273149251) ^ 113092250 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_282158414653 : Nat.Prime 282158414653 := by
  apply lucas_primality 282158414653 (2 : ZMod 282158414653)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (103, 1), (228283507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (103, 1), (228283507, 1)] : List FactorBlock).map factorBlockValue).prod) = 282158414653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_103
      · exact prime_eightyTwoCB_228283507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 282158414653) ^ 141079207326 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 282158414653) ^ 94052804884 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 282158414653) ^ 2739402084 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 282158414653) ^ 1236 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_289532763097 : Nat.Prime 289532763097 := by
  apply lucas_primality 289532763097 (5 : ZMod 289532763097)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (280555003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (280555003, 1)] : List FactorBlock).map factorBlockValue).prod) = 289532763097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_280555003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 289532763097) ^ 144766381548 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 289532763097) ^ 96510921032 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 289532763097) ^ 6733320072 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 289532763097) ^ 1032 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_300038345941 : Nat.Prime 300038345941 := by
  apply lucas_primality 300038345941 (6 : ZMod 300038345941)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (172435831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (172435831, 1)] : List FactorBlock).map factorBlockValue).prod) = 300038345941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_172435831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 300038345941) ^ 150019172970 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 300038345941) ^ 100012781980 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 300038345941) ^ 60007669188 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 300038345941) ^ 10346149860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 300038345941) ^ 1740 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_311940014227 : Nat.Prime 311940014227 := by
  apply lucas_primality 311940014227 (2 : ZMod 311940014227)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (51990002371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (51990002371, 1)] : List FactorBlock).map factorBlockValue).prod) = 311940014227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_51990002371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 311940014227) ^ 155970007113 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 311940014227) ^ 103980004742 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 311940014227) ^ 6 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_371902309301 : Nat.Prime 371902309301 := by
  apply lucas_primality 371902309301 (2 : ZMod 371902309301)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (1409, 1), (2639477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (1409, 1), (2639477, 1)] : List FactorBlock).map factorBlockValue).prod) = 371902309301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1409
      · exact prime_eightyTwoCB_2639477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 371902309301) ^ 185951154650 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 371902309301) ^ 74380461860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 371902309301) ^ 263947700 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 371902309301) ^ 140900 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_378676576571 : Nat.Prime 378676576571 := by
  apply lucas_primality 378676576571 (2 : ZMod 378676576571)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37867657657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37867657657, 1)] : List FactorBlock).map factorBlockValue).prod) = 378676576571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_37867657657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 378676576571) ^ 189338288285 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 378676576571) ^ 75735315314 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 378676576571) ^ 10 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_514734194687 : Nat.Prime 514734194687 := by
  apply lucas_primality 514734194687 (5 : ZMod 514734194687)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83089, 1), (3097487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83089, 1), (3097487, 1)] : List FactorBlock).map factorBlockValue).prod) = 514734194687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_83089
      · exact prime_eightyTwoCB_3097487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 514734194687) ^ 257367097343 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 514734194687) ^ 6194974 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 514734194687) ^ 166178 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_572229962443 : Nat.Prime 572229962443 := by
  apply lucas_primality 572229962443 (2 : ZMod 572229962443)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (3359, 1), (556723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (3359, 1), (556723, 1)] : List FactorBlock).map factorBlockValue).prod) = 572229962443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_3359
      · exact prime_eightyTwoCB_556723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 572229962443) ^ 286114981221 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 572229962443) ^ 190743320814 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 572229962443) ^ 33660586026 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 572229962443) ^ 170357238 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 572229962443) ^ 1027854 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_703081867001 : Nat.Prime 703081867001 := by
  apply lucas_primality 703081867001 (3 : ZMod 703081867001)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (703081867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (703081867, 1)] : List FactorBlock).map factorBlockValue).prod) = 703081867001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_703081867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 703081867001) ^ 351540933500 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 703081867001) ^ 140616373400 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 703081867001) ^ 1000 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_706170957847 : Nat.Prime 706170957847 := by
  apply lucas_primality 706170957847 (3 : ZMod 706170957847)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (1099954763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (1099954763, 1)] : List FactorBlock).map factorBlockValue).prod) = 706170957847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_107
      · exact prime_eightyTwoCB_1099954763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 706170957847) ^ 353085478923 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 706170957847) ^ 235390319282 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 706170957847) ^ 6599728578 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 706170957847) ^ 642 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_711992106983 : Nat.Prime 711992106983 := by
  apply lucas_primality 711992106983 (10 : ZMod 711992106983)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (31, 1), (73, 1), (711817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (31, 1), (73, 1), (711817, 1)] : List FactorBlock).map factorBlockValue).prod) = 711992106983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_711817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 711992106983) ^ 355996053491 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 711992106983) ^ 54768623614 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 711992106983) ^ 41881888646 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 711992106983) ^ 22967487322 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 711992106983) ^ 9753316534 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 711992106983) ^ 1000246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_728063044651 : Nat.Prime 728063044651 := by
  apply lucas_primality 728063044651 (3 : ZMod 728063044651)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (167, 1), (263, 1), (4093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (167, 1), (263, 1), (4093, 1)] : List FactorBlock).map factorBlockValue).prod) = 728063044651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_167
      · exact prime_eightyTwoCB_263
      · exact prime_eightyTwoCB_4093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 728063044651) ^ 364031522325 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 728063044651) ^ 242687681550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 728063044651) ^ 145612608930 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 728063044651) ^ 4359658950 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 728063044651) ^ 2768300550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 728063044651) ^ 177880050 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_802703468519 : Nat.Prime 802703468519 := by
  apply lucas_primality 802703468519 (7 : ZMod 802703468519)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (57335962037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (57335962037, 1)] : List FactorBlock).map factorBlockValue).prod) = 802703468519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_57335962037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 802703468519) ^ 401351734259 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 802703468519) ^ 114671924074 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 802703468519) ^ 14 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_815250253193 : Nat.Prime 815250253193 := by
  apply lucas_primality 815250253193 (3 : ZMod 815250253193)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101906281649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101906281649, 1)] : List FactorBlock).map factorBlockValue).prod) = 815250253193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_101906281649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 815250253193) ^ 407625126596 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 815250253193) ^ 8 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_925588449899 : Nat.Prime 925588449899 := by
  apply lucas_primality 925588449899 (2 : ZMod 925588449899)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (211, 1), (4951, 1), (9041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (211, 1), (4951, 1), (9041, 1)] : List FactorBlock).map factorBlockValue).prod) = 925588449899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_211
      · exact prime_eightyTwoCB_4951
      · exact prime_eightyTwoCB_9041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 925588449899) ^ 462794224949 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 925588449899) ^ 132226921414 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 925588449899) ^ 4386675118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 925588449899) ^ 186949798 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 925588449899) ^ 102376778 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1049189858329 : Nat.Prime 1049189858329 := by
  apply lucas_primality 1049189858329 (13 : ZMod 1049189858329)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (131, 1), (1409, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (131, 1), (1409, 1), (8167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1049189858329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_131
      · exact prime_eightyTwoCB_1409
      · exact prime_eightyTwoCB_8167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1049189858329) ^ 524594929164 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1049189858329) ^ 349729952776 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1049189858329) ^ 36178960632 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1049189858329) ^ 8009082888 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1049189858329) ^ 744634392 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 1049189858329) ^ 128466984 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1407739922761 : Nat.Prime 1407739922761 := by
  apply lucas_primality 1407739922761 (11 : ZMod 1407739922761)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11731166023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11731166023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1407739922761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11731166023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1407739922761) ^ 703869961380 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407739922761) ^ 469246640920 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407739922761) ^ 281547984552 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1407739922761) ^ 120 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1706219306873 : Nat.Prime 1706219306873 := by
  apply lucas_primality 1706219306873 (3 : ZMod 1706219306873)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (2396375431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (2396375431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706219306873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_89
      · exact prime_eightyTwoCB_2396375431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1706219306873) ^ 853109653436 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706219306873) ^ 19171003448 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706219306873) ^ 712 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1838459065357 : Nat.Prime 1838459065357 := by
  apply lucas_primality 1838459065357 (2 : ZMod 1838459065357)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (15187, 1), (3362633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (15187, 1), (3362633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1838459065357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_15187
      · exact prime_eightyTwoCB_3362633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1838459065357) ^ 919229532678 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838459065357) ^ 612819688452 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838459065357) ^ 121054788 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838459065357) ^ 546732 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2345119639757 : Nat.Prime 2345119639757 := by
  apply lucas_primality 2345119639757 (2 : ZMod 2345119639757)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (67, 1), (73, 1), (2550407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (67, 1), (73, 1), (2550407, 1)] : List FactorBlock).map factorBlockValue).prod) = 2345119639757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_47
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_2550407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2345119639757) ^ 1172559819878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345119639757) ^ 49896162548 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345119639757) ^ 35001785668 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345119639757) ^ 32124926572 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345119639757) ^ 919508 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2872634247929 : Nat.Prime 2872634247929 := by
  apply lucas_primality 2872634247929 (3 : ZMod 2872634247929)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (72937, 1), (4923143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (72937, 1), (4923143, 1)] : List FactorBlock).map factorBlockValue).prod) = 2872634247929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_72937
      · exact prime_eightyTwoCB_4923143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2872634247929) ^ 1436317123964 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2872634247929) ^ 39385144 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2872634247929) ^ 583496 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2975218474409 : Nat.Prime 2975218474409 := by
  apply lucas_primality 2975218474409 (3 : ZMod 2975218474409)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (371902309301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (371902309301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2975218474409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_371902309301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2975218474409) ^ 1487609237204 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2975218474409) ^ 8 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3046952089261 : Nat.Prime 3046952089261 := by
  apply lucas_primality 3046952089261 (7 : ZMod 3046952089261)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (1880834623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (1880834623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3046952089261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1880834623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3046952089261) ^ 1523476044630 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046952089261) ^ 1015650696420 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046952089261) ^ 609390417852 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046952089261) ^ 1620 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3190387946461 : Nat.Prime 3190387946461 := by
  apply lucas_primality 3190387946461 (2 : ZMod 3190387946461)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (107, 1), (3475141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (107, 1), (3475141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3190387946461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_107
      · exact prime_eightyTwoCB_3475141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3190387946461) ^ 1595193973230 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 1063462648820 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 638077589292 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 290035267860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 245414457420 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 29816709780 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3190387946461) ^ 918060 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3330678406903 : Nat.Prime 3330678406903 := by
  apply lucas_primality 3330678406903 (6 : ZMod 3330678406903)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (179, 1), (40275199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (179, 1), (40275199, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330678406903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_179
      · exact prime_eightyTwoCB_40275199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3330678406903) ^ 1665339203451 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330678406903) ^ 1110226135634 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330678406903) ^ 475811200986 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330678406903) ^ 302788946082 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330678406903) ^ 18607141938 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330678406903) ^ 82698 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3447187174987 : Nat.Prime 3447187174987 := by
  apply lucas_primality 3447187174987 (3 : ZMod 3447187174987)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (353, 1), (733, 1), (2220419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (353, 1), (733, 1), (2220419, 1)] : List FactorBlock).map factorBlockValue).prod) = 3447187174987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_353
      · exact prime_eightyTwoCB_733
      · exact prime_eightyTwoCB_2220419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3447187174987) ^ 1723593587493 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3447187174987) ^ 1149062391662 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3447187174987) ^ 9765402762 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3447187174987) ^ 4702847442 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3447187174987) ^ 1552494 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_4792691361841 : Nat.Prime 4792691361841 := by
  apply lucas_primality 4792691361841 (13 : ZMod 4792691361841)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19969547341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19969547341, 1)] : List FactorBlock).map factorBlockValue).prod) = 4792691361841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_19969547341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4792691361841) ^ 2396345680920 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 4792691361841) ^ 1597563787280 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 4792691361841) ^ 958538272368 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 4792691361841) ^ 240 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_5378698280113 : Nat.Prime 5378698280113 := by
  apply lucas_primality 5378698280113 (5 : ZMod 5378698280113)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (113, 1), (991647913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (113, 1), (991647913, 1)] : List FactorBlock).map factorBlockValue).prod) = 5378698280113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_113
      · exact prime_eightyTwoCB_991647913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5378698280113) ^ 2689349140056 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5378698280113) ^ 1792899426704 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5378698280113) ^ 47599099824 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 5378698280113) ^ 5424 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6840595738283 : Nat.Prime 6840595738283 := by
  apply lucas_primality 6840595738283 (2 : ZMod 6840595738283)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (7617589909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (7617589909, 1)] : List FactorBlock).map factorBlockValue).prod) = 6840595738283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_449
      · exact prime_eightyTwoCB_7617589909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6840595738283) ^ 3420297869141 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6840595738283) ^ 15235179818 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6840595738283) ^ 898 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7061709578471 : Nat.Prime 7061709578471 := by
  apply lucas_primality 7061709578471 (7 : ZMod 7061709578471)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (706170957847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (706170957847, 1)] : List FactorBlock).map factorBlockValue).prod) = 7061709578471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_706170957847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7061709578471) ^ 3530854789235 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7061709578471) ^ 1412341915694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7061709578471) ^ 10 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7544501172781 : Nat.Prime 7544501172781 := by
  apply lucas_primality 7544501172781 (6 : ZMod 7544501172781)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (853, 1), (1030847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (853, 1), (1030847, 1)] : List FactorBlock).map factorBlockValue).prod) = 7544501172781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_853
      · exact prime_eightyTwoCB_1030847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7544501172781) ^ 3772250586390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 2514833724260 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 1508900234556 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 685863742980 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 580346244060 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 8844667260 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 7544501172781) ^ 7318740 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7972250846519 : Nat.Prime 7972250846519 := by
  apply lucas_primality 7972250846519 (7 : ZMod 7972250846519)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (2657, 1), (5227301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (2657, 1), (5227301, 1)] : List FactorBlock).map factorBlockValue).prod) = 7972250846519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_2657
      · exact prime_eightyTwoCB_5227301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7972250846519) ^ 3986125423259 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7972250846519) ^ 1138892978074 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7972250846519) ^ 194445142598 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7972250846519) ^ 3000470774 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7972250846519) ^ 1525118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8692250847353 : Nat.Prime 8692250847353 := by
  apply lucas_primality 8692250847353 (3 : ZMod 8692250847353)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (593, 1), (761, 1), (2407703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (593, 1), (761, 1), (2407703, 1)] : List FactorBlock).map factorBlockValue).prod) = 8692250847353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_593
      · exact prime_eightyTwoCB_761
      · exact prime_eightyTwoCB_2407703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8692250847353) ^ 4346125423676 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8692250847353) ^ 14658095864 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8692250847353) ^ 11422143032 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 8692250847353) ^ 3610184 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11107061398789 : Nat.Prime 11107061398789 := by
  apply lucas_primality 11107061398789 (2 : ZMod 11107061398789)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (925588449899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (925588449899, 1)] : List FactorBlock).map factorBlockValue).prod) = 11107061398789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_925588449899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11107061398789) ^ 5553530699394 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11107061398789) ^ 3702353799596 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11107061398789) ^ 12 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11129919294709 : Nat.Prime 11129919294709 := by
  apply lucas_primality 11129919294709 (2 : ZMod 11129919294709)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (9973045963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (9973045963, 1)] : List FactorBlock).map factorBlockValue).prod) = 11129919294709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_9973045963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11129919294709) ^ 5564959647354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11129919294709) ^ 3709973098236 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11129919294709) ^ 359029654668 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11129919294709) ^ 1116 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11934432164339 : Nat.Prime 11934432164339 := by
  apply lucas_primality 11934432164339 (2 : ZMod 11934432164339)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (95789, 1), (62295421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (95789, 1), (62295421, 1)] : List FactorBlock).map factorBlockValue).prod) = 11934432164339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_95789
      · exact prime_eightyTwoCB_62295421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11934432164339) ^ 5967216082169 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11934432164339) ^ 124590842 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 11934432164339) ^ 191578 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_12614428472101 : Nat.Prime 12614428472101 := by
  apply lucas_primality 12614428472101 (18 : ZMod 12614428472101)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (3517, 1), (131381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (3517, 1), (131381, 1)] : List FactorBlock).map factorBlockValue).prod) = 12614428472101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_3517
      · exact prime_eightyTwoCB_131381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 12614428472101) ^ 6307214236050 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 4204809490700 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 2522885694420 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 1802061210300 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 970340651700 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 3586701300 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (18 : ZMod 12614428472101) ^ 96014100 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_12800018503061 : Nat.Prime 12800018503061 := by
  apply lucas_primality 12800018503061 (2 : ZMod 12800018503061)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (73, 1), (8767135961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (73, 1), (8767135961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12800018503061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_8767135961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12800018503061) ^ 6400009251530 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12800018503061) ^ 2560003700612 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12800018503061) ^ 175342719220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12800018503061) ^ 1460 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_13207456314911 : Nat.Prime 13207456314911 := by
  apply lucas_primality 13207456314911 (22 : ZMod 13207456314911)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (109, 1), (7993, 1), (10601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (109, 1), (7993, 1), (10601, 1)] : List FactorBlock).map factorBlockValue).prod) = 13207456314911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_109
      · exact prime_eightyTwoCB_7993
      · exact prime_eightyTwoCB_10601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 13207456314911) ^ 6603728157455 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 2641491262982 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 1200677846810 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 1015958178070 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 121169323990 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 1652377870 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (22 : ZMod 13207456314911) ^ 1245868910 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_13396713037723 : Nat.Prime 13396713037723 := by
  apply lucas_primality 13396713037723 (3 : ZMod 13396713037723)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (22063, 1), (4819069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (22063, 1), (4819069, 1)] : List FactorBlock).map factorBlockValue).prod) = 13396713037723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_22063
      · exact prime_eightyTwoCB_4819069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13396713037723) ^ 6698356518861 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13396713037723) ^ 4465571012574 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13396713037723) ^ 1913816148246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13396713037723) ^ 607202694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13396713037723) ^ 2779938 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_15944501693039 : Nat.Prime 15944501693039 := by
  apply lucas_primality 15944501693039 (17 : ZMod 15944501693039)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7972250846519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7972250846519, 1)] : List FactorBlock).map factorBlockValue).prod) = 15944501693039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7972250846519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 15944501693039) ^ 7972250846519 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 15944501693039) ^ 2 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_17981551341263 : Nat.Prime 17981551341263 := by
  apply lucas_primality 17981551341263 (5 : ZMod 17981551341263)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29927, 1), (300423553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29927, 1), (300423553, 1)] : List FactorBlock).map factorBlockValue).prod) = 17981551341263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_29927
      · exact prime_eightyTwoCB_300423553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17981551341263) ^ 8990775670631 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 17981551341263) ^ 600847106 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 17981551341263) ^ 59854 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_18242948839751 : Nat.Prime 18242948839751 := by
  apply lucas_primality 18242948839751 (29 : ZMod 18242948839751)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (72971795359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (72971795359, 1)] : List FactorBlock).map factorBlockValue).prod) = 18242948839751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_72971795359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 18242948839751) ^ 9121474419875 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (29 : ZMod 18242948839751) ^ 3648589767950 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (29 : ZMod 18242948839751) ^ 250 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_20236954983689 : Nat.Prime 20236954983689 := by
  apply lucas_primality 20236954983689 (3 : ZMod 20236954983689)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (643, 1), (3934089227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (643, 1), (3934089227, 1)] : List FactorBlock).map factorBlockValue).prod) = 20236954983689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_643
      · exact prime_eightyTwoCB_3934089227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20236954983689) ^ 10118477491844 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20236954983689) ^ 31472713816 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20236954983689) ^ 5144 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_24457507595791 : Nat.Prime 24457507595791 := by
  apply lucas_primality 24457507595791 (3 : ZMod 24457507595791)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (815250253193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (815250253193, 1)] : List FactorBlock).map factorBlockValue).prod) = 24457507595791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_815250253193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24457507595791) ^ 12228753797895 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 24457507595791) ^ 8152502531930 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 24457507595791) ^ 4891501519158 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 24457507595791) ^ 30 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_31744782992089 : Nat.Prime 31744782992089 := by
  apply lucas_primality 31744782992089 (7 : ZMod 31744782992089)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1213, 1), (363478783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1213, 1), (363478783, 1)] : List FactorBlock).map factorBlockValue).prod) = 31744782992089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_1213
      · exact prime_eightyTwoCB_363478783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31744782992089) ^ 15872391496044 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31744782992089) ^ 10581594330696 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31744782992089) ^ 26170472376 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 31744782992089) ^ 87336 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_33948182692939 : Nat.Prime 33948182692939 := by
  apply lucas_primality 33948182692939 (2 : ZMod 33948182692939)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (827, 1), (9359279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (827, 1), (9359279, 1)] : List FactorBlock).map factorBlockValue).prod) = 33948182692939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_827
      · exact prime_eightyTwoCB_9359279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33948182692939) ^ 16974091346469 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33948182692939) ^ 11316060897646 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33948182692939) ^ 1996951923114 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33948182692939) ^ 789492620766 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33948182692939) ^ 41049797694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33948182692939) ^ 3627222 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_40195508403049 : Nat.Prime 40195508403049 := by
  apply lucas_primality 40195508403049 (7 : ZMod 40195508403049)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (6553, 1), (1950989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (6553, 1), (1950989, 1)] : List FactorBlock).map factorBlockValue).prod) = 40195508403049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_131
      · exact prime_eightyTwoCB_6553
      · exact prime_eightyTwoCB_1950989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 40195508403049) ^ 20097754201524 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 40195508403049) ^ 13398502801016 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 40195508403049) ^ 306835942008 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 40195508403049) ^ 6133909416 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 40195508403049) ^ 20602632 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_43208760066397 : Nat.Prime 43208760066397 := by
  apply lucas_primality 43208760066397 (5 : ZMod 43208760066397)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1879, 1), (1916301227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1879, 1), (1916301227, 1)] : List FactorBlock).map factorBlockValue).prod) = 43208760066397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_1879
      · exact prime_eightyTwoCB_1916301227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43208760066397) ^ 21604380033198 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 43208760066397) ^ 14402920022132 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 43208760066397) ^ 22995614724 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 43208760066397) ^ 22548 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_53251156286737 : Nat.Prime 53251156286737 := by
  apply lucas_primality 53251156286737 (5 : ZMod 53251156286737)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (31, 1), (9127, 1), (206369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (31, 1), (9127, 1), (206369, 1)] : List FactorBlock).map factorBlockValue).prod) = 53251156286737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_9127
      · exact prime_eightyTwoCB_206369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53251156286737) ^ 26625578143368 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53251156286737) ^ 17750385428912 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53251156286737) ^ 2802692436144 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53251156286737) ^ 1717779235056 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53251156286737) ^ 5834464368 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53251156286737) ^ 258038544 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_60946217565049 : Nat.Prime 60946217565049 := by
  apply lucas_primality 60946217565049 (7 : ZMod 60946217565049)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (282158414653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (282158414653, 1)] : List FactorBlock).map factorBlockValue).prod) = 60946217565049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_282158414653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 60946217565049) ^ 30473108782524 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 60946217565049) ^ 20315405855016 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 60946217565049) ^ 216 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_71001698308003 : Nat.Prime 71001698308003 := by
  apply lucas_primality 71001698308003 (5 : ZMod 71001698308003)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (11, 1), (17, 1), (1381, 1), (242449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (11, 1), (17, 1), (1381, 1), (242449, 1)] : List FactorBlock).map factorBlockValue).prod) = 71001698308003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_1381
      · exact prime_eightyTwoCB_242449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 71001698308003) ^ 35500849154001 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 23667232769334 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 10143099758286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 6454699846182 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 4176570488706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 51413250042 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 71001698308003) ^ 292852098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_76227879121441 : Nat.Prime 76227879121441 := by
  apply lucas_primality 76227879121441 (7 : ZMod 76227879121441)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (1097, 1), (1181, 1), (122579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (1097, 1), (1181, 1), (122579, 1)] : List FactorBlock).map factorBlockValue).prod) = 76227879121441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1097
      · exact prime_eightyTwoCB_1181
      · exact prime_eightyTwoCB_122579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76227879121441) ^ 38113939560720 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 76227879121441) ^ 25409293040480 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 76227879121441) ^ 15245575824288 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 76227879121441) ^ 69487583520 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 76227879121441) ^ 64545198240 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 76227879121441) ^ 621867360 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_88012831107433 : Nat.Prime 88012831107433 := by
  apply lucas_primality 88012831107433 (5 : ZMod 88012831107433)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (163, 1), (292183993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (163, 1), (292183993, 1)] : List FactorBlock).map factorBlockValue).prod) = 88012831107433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_163
      · exact prime_eightyTwoCB_292183993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88012831107433) ^ 44006415553716 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88012831107433) ^ 29337610369144 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88012831107433) ^ 12573261586776 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88012831107433) ^ 8001166464312 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88012831107433) ^ 539956019064 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88012831107433) ^ 301224 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_92360856598939 : Nat.Prime 92360856598939 := by
  apply lucas_primality 92360856598939 (11 : ZMod 92360856598939)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (20981, 1), (244562161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (20981, 1), (244562161, 1)] : List FactorBlock).map factorBlockValue).prod) = 92360856598939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_20981
      · exact prime_eightyTwoCB_244562161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 92360856598939) ^ 46180428299469 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 92360856598939) ^ 30786952199646 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 92360856598939) ^ 4402118898 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 92360856598939) ^ 377658 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_93133135610309 : Nat.Prime 93133135610309 := by
  apply lucas_primality 93133135610309 (2 : ZMod 93133135610309)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21107, 1), (1103107211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21107, 1), (1103107211, 1)] : List FactorBlock).map factorBlockValue).prod) = 93133135610309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_21107
      · exact prime_eightyTwoCB_1103107211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93133135610309) ^ 46566567805154 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93133135610309) ^ 4412428844 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93133135610309) ^ 84428 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_104853435850069 : Nat.Prime 104853435850069 := by
  apply lucas_primality 104853435850069 (2 : ZMod 104853435850069)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (239, 1), (4759, 1), (7682239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (239, 1), (4759, 1), (7682239, 1)] : List FactorBlock).map factorBlockValue).prod) = 104853435850069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_239
      · exact prime_eightyTwoCB_4759
      · exact prime_eightyTwoCB_7682239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104853435850069) ^ 52426717925034 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104853435850069) ^ 34951145283356 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104853435850069) ^ 438717304812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104853435850069) ^ 22032661452 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104853435850069) ^ 13648812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_231457578257183 : Nat.Prime 231457578257183 := by
  apply lucas_primality 231457578257183 (5 : ZMod 231457578257183)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1373, 1), (38783, 1), (50543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1373, 1), (38783, 1), (50543, 1)] : List FactorBlock).map factorBlockValue).prod) = 231457578257183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_1373
      · exact prime_eightyTwoCB_38783
      · exact prime_eightyTwoCB_50543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 231457578257183) ^ 115728789128591 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 231457578257183) ^ 5382734378074 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 231457578257183) ^ 168577988534 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 231457578257183) ^ 5968016354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 231457578257183) ^ 4579419074 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_310480639447519 : Nat.Prime 310480639447519 := by
  apply lucas_primality 310480639447519 (3 : ZMod 310480639447519)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (23990159129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (23990159129, 1)] : List FactorBlock).map factorBlockValue).prod) = 310480639447519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_719
      · exact prime_eightyTwoCB_23990159129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 310480639447519) ^ 155240319723759 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 310480639447519) ^ 103493546482506 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 310480639447519) ^ 431822864322 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 310480639447519) ^ 12942 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_389891608199689 : Nat.Prime 389891608199689 := by
  apply lucas_primality 389891608199689 (13 : ZMod 389891608199689)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (37, 1), (8960553599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (37, 1), (8960553599, 1)] : List FactorBlock).map factorBlockValue).prod) = 389891608199689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_8960553599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 389891608199689) ^ 194945804099844 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 389891608199689) ^ 129963869399896 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 389891608199689) ^ 55698801171384 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 389891608199689) ^ 10537611032424 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 389891608199689) ^ 43512 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_496295263845083 : Nat.Prime 496295263845083 := by
  apply lucas_primality 496295263845083 (2 : ZMod 496295263845083)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (179, 1), (197, 1), (5323, 1), (101693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (179, 1), (197, 1), (5323, 1), (101693, 1)] : List FactorBlock).map factorBlockValue).prod) = 496295263845083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_179
      · exact prime_eightyTwoCB_197
      · exact prime_eightyTwoCB_5323
      · exact prime_eightyTwoCB_101693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 496295263845083) ^ 248147631922541 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 496295263845083) ^ 38176558757314 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 496295263845083) ^ 2772599239358 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 496295263845083) ^ 2519265298706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 496295263845083) ^ 93236006734 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 496295263845083) ^ 4880328674 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_591877210255909 : Nat.Prime 591877210255909 := by
  apply lucas_primality 591877210255909 (2 : ZMod 591877210255909)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (181, 1), (331, 1), (43330151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (181, 1), (331, 1), (43330151, 1)] : List FactorBlock).map factorBlockValue).prod) = 591877210255909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_181
      · exact prime_eightyTwoCB_331
      · exact prime_eightyTwoCB_43330151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 591877210255909) ^ 295938605127954 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 591877210255909) ^ 197292403418636 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 591877210255909) ^ 31151432118732 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 591877210255909) ^ 3270039835668 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 591877210255909) ^ 1788148671468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 591877210255909) ^ 13659708 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_680664454275749 : Nat.Prime 680664454275749 := by
  apply lucas_primality 680664454275749 (2 : ZMod 680664454275749)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239, 1), (711992106983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239, 1), (711992106983, 1)] : List FactorBlock).map factorBlockValue).prod) = 680664454275749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_239
      · exact prime_eightyTwoCB_711992106983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 680664454275749) ^ 340332227137874 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 680664454275749) ^ 2847968427932 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 680664454275749) ^ 956 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_737698055447219 : Nat.Prime 737698055447219 := by
  apply lucas_primality 737698055447219 (2 : ZMod 737698055447219)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (3447187174987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (3447187174987, 1)] : List FactorBlock).map factorBlockValue).prod) = 737698055447219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_107
      · exact prime_eightyTwoCB_3447187174987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 737698055447219) ^ 368849027723609 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 737698055447219) ^ 6894374349974 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 737698055447219) ^ 214 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_798741353619631 : Nat.Prime 798741353619631 := by
  apply lucas_primality 798741353619631 (3 : ZMod 798741353619631)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (613, 1), (1123, 1), (12892093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (613, 1), (1123, 1), (12892093, 1)] : List FactorBlock).map factorBlockValue).prod) = 798741353619631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_613
      · exact prime_eightyTwoCB_1123
      · exact prime_eightyTwoCB_12892093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 798741353619631) ^ 399370676809815 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 798741353619631) ^ 266247117873210 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 798741353619631) ^ 159748270723926 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 798741353619631) ^ 1303003839510 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 798741353619631) ^ 711256770810 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 798741353619631) ^ 61955910 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1019369234927227 : Nat.Prime 1019369234927227 := by
  apply lucas_primality 1019369234927227 (3 : ZMod 1019369234927227)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (197, 1), (23308392439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (197, 1), (23308392439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1019369234927227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_197
      · exact prime_eightyTwoCB_23308392439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1019369234927227) ^ 509684617463613 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019369234927227) ^ 339789744975742 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019369234927227) ^ 27550519862898 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019369234927227) ^ 5174463121458 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019369234927227) ^ 43734 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1339338142215277 : Nat.Prime 1339338142215277 := by
  apply lucas_primality 1339338142215277 (6 : ZMod 1339338142215277)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (15944501693039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (15944501693039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1339338142215277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_15944501693039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1339338142215277) ^ 669669071107638 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1339338142215277) ^ 446446047405092 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1339338142215277) ^ 191334020316468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1339338142215277) ^ 84 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1406617802265733 : Nat.Prime 1406617802265733 := by
  apply lucas_primality 1406617802265733 (2 : ZMod 1406617802265733)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (728063044651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (728063044651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406617802265733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_728063044651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406617802265733) ^ 703308901132866 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406617802265733) ^ 468872600755244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406617802265733) ^ 200945400323676 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406617802265733) ^ 61157295750684 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406617802265733) ^ 1932 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2319680071050479 : Nat.Prime 2319680071050479 := by
  apply lucas_primality 2319680071050479 (7 : ZMod 2319680071050479)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (872203, 1), (1329782213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (872203, 1), (1329782213, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319680071050479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_872203
      · exact prime_eightyTwoCB_1329782213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2319680071050479) ^ 1159840035525239 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2319680071050479) ^ 2659564426 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2319680071050479) ^ 1744406 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_4004819686857343 : Nat.Prime 4004819686857343 := by
  apply lucas_primality 4004819686857343 (3 : ZMod 4004819686857343)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (7307, 1), (3971593337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (7307, 1), (3971593337, 1)] : List FactorBlock).map factorBlockValue).prod) = 4004819686857343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_7307
      · exact prime_eightyTwoCB_3971593337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4004819686857343) ^ 2002409843428671 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4004819686857343) ^ 1334939895619114 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4004819686857343) ^ 174122595080754 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4004819686857343) ^ 548079880506 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4004819686857343) ^ 1008366 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6468124963365167 : Nat.Prime 6468124963365167 := by
  apply lucas_primality 6468124963365167 (5 : ZMod 6468124963365167)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1087, 1), (2975218474409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1087, 1), (2975218474409, 1)] : List FactorBlock).map factorBlockValue).prod) = 6468124963365167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_1087
      · exact prime_eightyTwoCB_2975218474409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6468124963365167) ^ 3234062481682583 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6468124963365167) ^ 5950436948818 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6468124963365167) ^ 2174 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7549447381204969 : Nat.Prime 7549447381204969 := by
  apply lucas_primality 7549447381204969 (19 : ZMod 7549447381204969)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (104853435850069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (104853435850069, 1)] : List FactorBlock).map factorBlockValue).prod) = 7549447381204969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_104853435850069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 7549447381204969) ^ 3774723690602484 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7549447381204969) ^ 2516482460401656 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7549447381204969) ^ 72 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8080913518165127 : Nat.Prime 8080913518165127 := by
  apply lucas_primality 8080913518165127 (5 : ZMod 8080913518165127)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26189, 1), (154280681167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26189, 1), (154280681167, 1)] : List FactorBlock).map factorBlockValue).prod) = 8080913518165127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_26189
      · exact prime_eightyTwoCB_154280681167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8080913518165127) ^ 4040456759082563 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8080913518165127) ^ 308561362334 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8080913518165127) ^ 52378 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8425668878709889 : Nat.Prime 8425668878709889 := by
  apply lucas_primality 8425668878709889 (17 : ZMod 8425668878709889)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (263, 1), (6417620953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (263, 1), (6417620953, 1)] : List FactorBlock).map factorBlockValue).prod) = 8425668878709889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_263
      · exact prime_eightyTwoCB_6417620953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 8425668878709889) ^ 4212834439354944 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 8425668878709889) ^ 2808556292903296 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 8425668878709889) ^ 648128375285376 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 8425668878709889) ^ 32036763797376 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (17 : ZMod 8425668878709889) ^ 1312896 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_8703955645749691 : Nat.Prime 8703955645749691 := by
  apply lucas_primality 8703955645749691 (2 : ZMod 8703955645749691)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (12614428472101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (12614428472101, 1)] : List FactorBlock).map factorBlockValue).prod) = 8703955645749691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_12614428472101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8703955645749691) ^ 4351977822874845 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8703955645749691) ^ 2901318548583230 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8703955645749691) ^ 1740791129149938 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8703955645749691) ^ 378432854163030 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8703955645749691) ^ 690 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_10284974776368613 : Nat.Prime 10284974776368613 := by
  apply lucas_primality 10284974776368613 (2 : ZMod 10284974776368613)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (269, 1), (569, 1), (9343, 1), (66593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (269, 1), (569, 1), (9343, 1), (66593, 1)] : List FactorBlock).map factorBlockValue).prod) = 10284974776368613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_269
      · exact prime_eightyTwoCB_569
      · exact prime_eightyTwoCB_9343
      · exact prime_eightyTwoCB_66593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10284974776368613) ^ 5142487388184306 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284974776368613) ^ 3428324925456204 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284974776368613) ^ 38234106975348 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284974776368613) ^ 18075526847748 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284974776368613) ^ 1100821446684 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10284974776368613) ^ 154445283684 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_13357700358950837 : Nat.Prime 13357700358950837 := by
  apply lucas_primality 13357700358950837 (2 : ZMod 13357700358950837)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (2089, 1), (55243, 1), (133351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (2089, 1), (55243, 1), (133351, 1)] : List FactorBlock).map factorBlockValue).prod) = 13357700358950837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_2089
      · exact prime_eightyTwoCB_55243
      · exact prime_eightyTwoCB_133351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13357700358950837) ^ 6678850179475418 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13357700358950837) ^ 1908242908421548 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13357700358950837) ^ 430893559966156 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13357700358950837) ^ 6394303666324 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13357700358950837) ^ 241798967452 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 13357700358950837) ^ 100169480236 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_13760901555641657 : Nat.Prime 13760901555641657 := by
  apply lucas_primality 13760901555641657 (3 : ZMod 13760901555641657)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (29, 1), (89, 1), (60457, 1), (847967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (29, 1), (89, 1), (60457, 1), (847967, 1)] : List FactorBlock).map factorBlockValue).prod) = 13760901555641657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_89
      · exact prime_eightyTwoCB_60457
      · exact prime_eightyTwoCB_847967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13760901555641657) ^ 6880450777820828 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13760901555641657) ^ 1058530888895512 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13760901555641657) ^ 474513846746264 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13760901555641657) ^ 154616871411704 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13760901555641657) ^ 227614694008 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 13760901555641657) ^ 16228109768 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_14011190678752819 : Nat.Prime 14011190678752819 := by
  apply lucas_primality 14011190678752819 (2 : ZMod 14011190678752819)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (181, 1), (300038345941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (181, 1), (300038345941, 1)] : List FactorBlock).map factorBlockValue).prod) = 14011190678752819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_181
      · exact prime_eightyTwoCB_300038345941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14011190678752819) ^ 7005595339376409 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14011190678752819) ^ 4670396892917606 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14011190678752819) ^ 325841643691926 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14011190678752819) ^ 77409893252778 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 14011190678752819) ^ 46698 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_16666951265252723 : Nat.Prime 16666951265252723 := by
  apply lucas_primality 16666951265252723 (2 : ZMod 16666951265252723)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (53, 1), (58207, 1), (55128859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (53, 1), (58207, 1), (55128859, 1)] : List FactorBlock).map factorBlockValue).prod) = 16666951265252723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_53
      · exact prime_eightyTwoCB_58207
      · exact prime_eightyTwoCB_55128859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16666951265252723) ^ 8333475632626361 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16666951265252723) ^ 2380993037893246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16666951265252723) ^ 314470778589674 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16666951265252723) ^ 286339293646 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 16666951265252723) ^ 302327158 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_29359862262460649 : Nat.Prime 29359862262460649 := by
  apply lucas_primality 29359862262460649 (3 : ZMod 29359862262460649)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (251, 1), (15881, 1), (920687951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (251, 1), (15881, 1), (920687951, 1)] : List FactorBlock).map factorBlockValue).prod) = 29359862262460649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_251
      · exact prime_eightyTwoCB_15881
      · exact prime_eightyTwoCB_920687951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29359862262460649) ^ 14679931131230324 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 29359862262460649) ^ 116971562798648 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 29359862262460649) ^ 1848741405608 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 29359862262460649) ^ 31889048 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_34428017719943779 : Nat.Prime 34428017719943779 := by
  apply lucas_primality 34428017719943779 (3 : ZMod 34428017719943779)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7927, 1), (103407935867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7927, 1), (103407935867, 1)] : List FactorBlock).map factorBlockValue).prod) = 34428017719943779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_7927
      · exact prime_eightyTwoCB_103407935867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34428017719943779) ^ 17214008859971889 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34428017719943779) ^ 11476005906647926 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34428017719943779) ^ 4918288245706254 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34428017719943779) ^ 4343133306414 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 34428017719943779) ^ 332934 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_60744484562731451 : Nat.Prime 60744484562731451 := by
  apply lucas_primality 60744484562731451 (2 : ZMod 60744484562731451)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (59, 1), (167, 1), (13159, 1), (720779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (59, 1), (167, 1), (13159, 1), (720779, 1)] : List FactorBlock).map factorBlockValue).prod) = 60744484562731451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_167
      · exact prime_eightyTwoCB_13159
      · exact prime_eightyTwoCB_720779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60744484562731451) ^ 30372242281365725 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 12148896912546290 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 4672652658671650 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 1029567534961550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 363739428519350 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 4616193066550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 60744484562731451) ^ 84276157550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_82610282233036541 : Nat.Prime 82610282233036541 := by
  apply lucas_primality 82610282233036541 (10 : ZMod 82610282233036541)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (3931, 1), (3028109611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (3931, 1), (3028109611, 1)] : List FactorBlock).map factorBlockValue).prod) = 82610282233036541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_347
      · exact prime_eightyTwoCB_3931
      · exact prime_eightyTwoCB_3028109611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 82610282233036541) ^ 41305141116518270 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 82610282233036541) ^ 16522056446607308 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 82610282233036541) ^ 238069977616820 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 82610282233036541) ^ 21015080700340 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 82610282233036541) ^ 27281140 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_114386723181163567 : Nat.Prime 114386723181163567 := by
  apply lucas_primality 114386723181163567 (6 : ZMod 114386723181163567)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (3967, 1), (33287, 1), (254627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (3967, 1), (33287, 1), (254627, 1)] : List FactorBlock).map factorBlockValue).prod) = 114386723181163567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_3967
      · exact prime_eightyTwoCB_33287
      · exact prime_eightyTwoCB_254627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 114386723181163567) ^ 57193361590581783 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 114386723181163567) ^ 38128907727054522 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 114386723181163567) ^ 16340960454451938 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 114386723181163567) ^ 28834565964498 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 114386723181163567) ^ 3436378261218 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 114386723181163567) ^ 449232497658 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_133662080072644241 : Nat.Prime 133662080072644241 := by
  apply lucas_primality 133662080072644241 (6 : ZMod 133662080072644241)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (43, 1), (109, 1), (27420787463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (43, 1), (109, 1), (27420787463, 1)] : List FactorBlock).map factorBlockValue).prod) = 133662080072644241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_109
      · exact prime_eightyTwoCB_27420787463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 133662080072644241) ^ 66831040036322120 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 133662080072644241) ^ 26732416014528848 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 133662080072644241) ^ 10281698467126480 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 133662080072644241) ^ 3108420466805680 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 133662080072644241) ^ 1226257615345360 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 133662080072644241) ^ 4874480 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_225008807892166537 : Nat.Prime 225008807892166537 := by
  apply lucas_primality 225008807892166537 (10 : ZMod 225008807892166537)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1339338142215277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1339338142215277, 1)] : List FactorBlock).map factorBlockValue).prod) = 225008807892166537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_1339338142215277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 225008807892166537) ^ 112504403946083268 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 225008807892166537) ^ 75002935964055512 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 225008807892166537) ^ 32144115413166648 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 225008807892166537) ^ 168 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_386041703538903509 : Nat.Prime 386041703538903509 := by
  apply lucas_primality 386041703538903509 (2 : ZMod 386041703538903509)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (383, 1), (1407739922761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (383, 1), (1407739922761, 1)] : List FactorBlock).map factorBlockValue).prod) = 386041703538903509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_179
      · exact prime_eightyTwoCB_383
      · exact prime_eightyTwoCB_1407739922761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 386041703538903509) ^ 193020851769451754 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 386041703538903509) ^ 2156657561669852 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 386041703538903509) ^ 1007941784696876 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 386041703538903509) ^ 274228 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2173303410323143543 : Nat.Prime 2173303410323143543 := by
  apply lucas_primality 2173303410323143543 (3 : ZMod 2173303410323143543)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (75577, 1), (4792691361841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (75577, 1), (4792691361841, 1)] : List FactorBlock).map factorBlockValue).prod) = 2173303410323143543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_75577
      · exact prime_eightyTwoCB_4792691361841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2173303410323143543) ^ 1086651705161571771 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173303410323143543) ^ 724434470107714514 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173303410323143543) ^ 28756148171046 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2173303410323143543) ^ 453462 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3302616373353997681 : Nat.Prime 3302616373353997681 := by
  apply lucas_primality 3302616373353997681 (19 : ZMod 3302616373353997681)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13760901555641657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13760901555641657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3302616373353997681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13760901555641657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3302616373353997681) ^ 1651308186676998840 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 3302616373353997681) ^ 1100872124451332560 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 3302616373353997681) ^ 660523274670799536 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (19 : ZMod 3302616373353997681) ^ 240 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7656783064031213039 : Nat.Prime 7656783064031213039 := by
  apply lucas_primality 7656783064031213039 (7 : ZMod 7656783064031213039)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (1553, 1), (11003, 1), (1061821031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (1553, 1), (11003, 1), (1061821031, 1)] : List FactorBlock).map factorBlockValue).prod) = 7656783064031213039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_211
      · exact prime_eightyTwoCB_1553
      · exact prime_eightyTwoCB_11003
      · exact prime_eightyTwoCB_1061821031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7656783064031213039) ^ 3828391532015606519 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7656783064031213039) ^ 36288071393512858 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7656783064031213039) ^ 4930317491327246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7656783064031213039) ^ 695881401802346 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7656783064031213039) ^ 7210992098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_10480370627707108613 : Nat.Prime 10480370627707108613 := by
  apply lucas_primality 10480370627707108613 (2 : ZMod 10480370627707108613)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (14011190678752819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (14011190678752819, 1)] : List FactorBlock).map factorBlockValue).prod) = 10480370627707108613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_14011190678752819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10480370627707108613) ^ 5240185313853554306 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10480370627707108613) ^ 952760966155191692 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10480370627707108613) ^ 616492389865124036 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10480370627707108613) ^ 748 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_15315415687503786587 : Nat.Prime 15315415687503786587 := by
  apply lucas_primality 15315415687503786587 (2 : ZMod 15315415687503786587)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (880981, 1), (8692250847353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (880981, 1), (8692250847353, 1)] : List FactorBlock).map factorBlockValue).prod) = 15315415687503786587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_880981
      · exact prime_eightyTwoCB_8692250847353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15315415687503786587) ^ 7657707843751893293 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15315415687503786587) ^ 17384501694706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15315415687503786587) ^ 1761962 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_19950988930779576749 : Nat.Prime 19950988930779576749 := by
  apply lucas_primality 19950988930779576749 (11 : ZMod 19950988930779576749)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (241, 1), (499, 1), (3190387946461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (241, 1), (499, 1), (3190387946461, 1)] : List FactorBlock).map factorBlockValue).prod) = 19950988930779576749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_241
      · exact prime_eightyTwoCB_499
      · exact prime_eightyTwoCB_3190387946461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 19950988930779576749) ^ 9975494465389788374 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 19950988930779576749) ^ 1534691456213813596 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 19950988930779576749) ^ 82784186434770028 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 19950988930779576749) ^ 39981941745049252 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 19950988930779576749) ^ 6253468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_33817076456151626003 : Nat.Prime 33817076456151626003 := by
  apply lucas_primality 33817076456151626003 (2 : ZMod 33817076456151626003)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (940327, 1), (17981551341263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (940327, 1), (17981551341263, 1)] : List FactorBlock).map factorBlockValue).prod) = 33817076456151626003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_940327
      · exact prime_eightyTwoCB_17981551341263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33817076456151626003) ^ 16908538228075813001 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33817076456151626003) ^ 35963102682526 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 33817076456151626003) ^ 1880654 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_42206138321874189317 : Nat.Prime 42206138321874189317 := by
  apply lucas_primality 42206138321874189317 (2 : ZMod 42206138321874189317)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (2800823, 1), (7230898063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (2800823, 1), (7230898063, 1)] : List FactorBlock).map factorBlockValue).prod) = 42206138321874189317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_521
      · exact prime_eightyTwoCB_2800823
      · exact prime_eightyTwoCB_7230898063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42206138321874189317) ^ 21103069160937094658 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 42206138321874189317) ^ 81009862422023396 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 42206138321874189317) ^ 15069191563292 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 42206138321874189317) ^ 5836915132 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_49846693903640695849 : Nat.Prime 49846693903640695849 := by
  apply lucas_primality 49846693903640695849 (11 : ZMod 49846693903640695849)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (97, 1), (101081, 1), (211828237711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (97, 1), (101081, 1), (211828237711, 1)] : List FactorBlock).map factorBlockValue).prod) = 49846693903640695849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_97
      · exact prime_eightyTwoCB_101081
      · exact prime_eightyTwoCB_211828237711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49846693903640695849) ^ 24923346951820347924 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 49846693903640695849) ^ 16615564634546898616 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 49846693903640695849) ^ 513883442305574184 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 49846693903640695849) ^ 493136137391208 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (11 : ZMod 49846693903640695849) ^ 235316568 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_74176390614546837343 : Nat.Prime 74176390614546837343 := by
  apply lucas_primality 74176390614546837343 (3 : ZMod 74176390614546837343)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (152407, 1), (223461601577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (152407, 1), (223461601577, 1)] : List FactorBlock).map factorBlockValue).prod) = 74176390614546837343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_152407
      · exact prime_eightyTwoCB_223461601577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 74176390614546837343) ^ 37088195307273418671 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 74176390614546837343) ^ 24725463538182279114 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 74176390614546837343) ^ 6743308237686076122 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 74176390614546837343) ^ 486699368234706 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 74176390614546837343) ^ 331942446 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_82481028214823640449 : Nat.Prime 82481028214823640449 := by
  apply lucas_primality 82481028214823640449 (3 : ZMod 82481028214823640449)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (109147, 1), (165587, 1), (35653819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (109147, 1), (165587, 1), (35653819, 1)] : List FactorBlock).map factorBlockValue).prod) = 82481028214823640449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_109147
      · exact prime_eightyTwoCB_165587
      · exact prime_eightyTwoCB_35653819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82481028214823640449) ^ 41240514107411820224 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 82481028214823640449) ^ 755687542624384 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 82481028214823640449) ^ 498112944946304 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 82481028214823640449) ^ 2313385508992 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_88185244649680905439 : Nat.Prime 88185244649680905439 := by
  apply lucas_primality 88185244649680905439 (13 : ZMod 88185244649680905439)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7994489, 1), (1838459065357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7994489, 1), (1838459065357, 1)] : List FactorBlock).map factorBlockValue).prod) = 88185244649680905439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7994489
      · exact prime_eightyTwoCB_1838459065357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 88185244649680905439) ^ 44092622324840452719 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 88185244649680905439) ^ 29395081549893635146 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 88185244649680905439) ^ 11030754392142 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 88185244649680905439) ^ 47966934 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_97039307342868248971 : Nat.Prime 97039307342868248971 := by
  apply lucas_primality 97039307342868248971 (2 : ZMod 97039307342868248971)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2847323, 1), (378676576571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2847323, 1), (378676576571, 1)] : List FactorBlock).map factorBlockValue).prod) = 97039307342868248971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_2847323
      · exact prime_eightyTwoCB_378676576571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97039307342868248971) ^ 48519653671434124485 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97039307342868248971) ^ 32346435780956082990 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97039307342868248971) ^ 19407861468573649794 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97039307342868248971) ^ 34080891891390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97039307342868248971) ^ 256259070 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_117611074896386261347 : Nat.Prime 117611074896386261347 := by
  apply lucas_primality 117611074896386261347 (2 : ZMod 117611074896386261347)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (714869, 1), (703081867001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (714869, 1), (703081867001, 1)] : List FactorBlock).map factorBlockValue).prod) = 117611074896386261347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_714869
      · exact prime_eightyTwoCB_703081867001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117611074896386261347) ^ 58805537448193130673 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117611074896386261347) ^ 39203691632128753782 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117611074896386261347) ^ 9047005761260481642 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117611074896386261347) ^ 164521156878234 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117611074896386261347) ^ 167279346 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_147553962236556534709 : Nat.Prime 147553962236556534709 := by
  apply lucas_primality 147553962236556534709 (2 : ZMod 147553962236556534709)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (19, 1), (181, 1), (15377, 1), (52967, 1), (89591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (19, 1), (181, 1), (15377, 1), (52967, 1), (89591, 1)] : List FactorBlock).map factorBlockValue).prod) = 147553962236556534709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_181
      · exact prime_eightyTwoCB_15377
      · exact prime_eightyTwoCB_52967
      · exact prime_eightyTwoCB_89591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147553962236556534709) ^ 73776981118278267354 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 49184654078852178236 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 21079137462365219244 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 7765998012450343932 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 815215260975450468 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 9595757445311604 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 2785771560340524 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 147553962236556534709) ^ 1646973046807788 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_296561908650660046157 : Nat.Prime 296561908650660046157 := by
  apply lucas_primality 296561908650660046157 (2 : ZMod 296561908650660046157)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3229, 1), (11329, 1), (289532763097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3229, 1), (11329, 1), (289532763097, 1)] : List FactorBlock).map factorBlockValue).prod) = 296561908650660046157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_3229
      · exact prime_eightyTwoCB_11329
      · exact prime_eightyTwoCB_289532763097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 296561908650660046157) ^ 148280954325330023078 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 296561908650660046157) ^ 42365986950094292308 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 296561908650660046157) ^ 91843266847525564 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 296561908650660046157) ^ 26177236177125964 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 296561908650660046157) ^ 1024277548 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_339205794715174821163 : Nat.Prime 339205794715174821163 := by
  apply lucas_primality 339205794715174821163 (2 : ZMod 339205794715174821163)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (839, 1), (20231, 1), (3330678406903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (839, 1), (20231, 1), (3330678406903, 1)] : List FactorBlock).map factorBlockValue).prod) = 339205794715174821163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_839
      · exact prime_eightyTwoCB_20231
      · exact prime_eightyTwoCB_3330678406903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 339205794715174821163) ^ 169602897357587410581 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 339205794715174821163) ^ 113068598238391607054 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 339205794715174821163) ^ 404297729100327558 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 339205794715174821163) ^ 16766635100349702 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 339205794715174821163) ^ 101842854 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_443412808904532703883 : Nat.Prime 443412808904532703883 := by
  apply lucas_primality 443412808904532703883 (2 : ZMod 443412808904532703883)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31395571, 1), (7061709578471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31395571, 1), (7061709578471, 1)] : List FactorBlock).map factorBlockValue).prod) = 443412808904532703883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_31395571
      · exact prime_eightyTwoCB_7061709578471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 443412808904532703883) ^ 221706404452266351941 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 443412808904532703883) ^ 14123419156942 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 443412808904532703883) ^ 62791142 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_477826348840075647809 : Nat.Prime 477826348840075647809 := by
  apply lucas_primality 477826348840075647809 (3 : ZMod 477826348840075647809)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 2), (17, 2), (73, 1), (139, 1), (2239, 1), (9397561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 2), (17, 2), (73, 1), (139, 1), (2239, 1), (9397561, 1)] : List FactorBlock).map factorBlockValue).prod) = 477826348840075647809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_17
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_139
      · exact prime_eightyTwoCB_2239
      · exact prime_eightyTwoCB_9397561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 477826348840075647809) ^ 238913174420037823904 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 43438758985461422528 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 28107432284710332224 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 6545566422466789696 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 3437599631942990272 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 213410606895969472 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 477826348840075647809) ^ 50845783160128 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1168244629030088580031 : Nat.Prime 1168244629030088580031 := by
  apply lucas_primality 1168244629030088580031 (3 : ZMod 1168244629030088580031)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (3109259, 1), (176399475509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (3109259, 1), (176399475509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1168244629030088580031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_71
      · exact prime_eightyTwoCB_3109259
      · exact prime_eightyTwoCB_176399475509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1168244629030088580031) ^ 584122314515044290015 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1168244629030088580031) ^ 389414876343362860010 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1168244629030088580031) ^ 233648925806017716006 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1168244629030088580031) ^ 16454149704649134930 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1168244629030088580031) ^ 375730882834170 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1168244629030088580031) ^ 6622721670 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1681699469029316808923 : Nat.Prime 1681699469029316808923 := by
  apply lucas_primality 1681699469029316808923 (2 : ZMod 1681699469029316808923)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (165779, 1), (5378698280113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (165779, 1), (5378698280113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1681699469029316808923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_165779
      · exact prime_eightyTwoCB_5378698280113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1681699469029316808923) ^ 840849734514658404461 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1681699469029316808923) ^ 73117368218665948214 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1681699469029316808923) ^ 41017060220227239242 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1681699469029316808923) ^ 10144224956293118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1681699469029316808923) ^ 312659194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1885218998852183177947 : Nat.Prime 1885218998852183177947 := by
  apply lucas_primality 1885218998852183177947 (7 : ZMod 1885218998852183177947)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (31, 1), (2221, 1), (93133135610309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (31, 1), (2221, 1), (93133135610309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1885218998852183177947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_2221
      · exact prime_eightyTwoCB_93133135610309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1885218998852183177947) ^ 942609499426091588973 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1885218998852183177947) ^ 628406332950727725982 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1885218998852183177947) ^ 269316999836026168278 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1885218998852183177947) ^ 60813516092005908966 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1885218998852183177947) ^ 848815397952356226 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1885218998852183177947) ^ 20242194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2563322219749667798003 : Nat.Prime 2563322219749667798003 := by
  apply lucas_primality 2563322219749667798003 (5 : ZMod 2563322219749667798003)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (13063, 1), (737698055447219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (13063, 1), (737698055447219, 1)] : List FactorBlock).map factorBlockValue).prod) = 2563322219749667798003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_13063
      · exact prime_eightyTwoCB_737698055447219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2563322219749667798003) ^ 1281661109874833899001 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2563322219749667798003) ^ 366188888535666828286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2563322219749667798003) ^ 134911695776298305158 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2563322219749667798003) ^ 196227682748960254 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2563322219749667798003) ^ 3474758 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2948729784038316035491 : Nat.Prime 2948729784038316035491 := by
  apply lucas_primality 2948729784038316035491 (10 : ZMod 2948729784038316035491)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (204163, 1), (16050719, 1), (29994539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (204163, 1), (16050719, 1), (29994539, 1)] : List FactorBlock).map factorBlockValue).prod) = 2948729784038316035491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_204163
      · exact prime_eightyTwoCB_16050719
      · exact prime_eightyTwoCB_29994539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2948729784038316035491) ^ 1474364892019158017745 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 2948729784038316035491) ^ 982909928012772011830 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 2948729784038316035491) ^ 589745956807663207098 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 2948729784038316035491) ^ 14443017510706230 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 2948729784038316035491) ^ 183713251975710 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 2948729784038316035491) ^ 98308888295910 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_3385993424237981517731 : Nat.Prime 3385993424237981517731 := by
  apply lucas_primality 3385993424237981517731 (2 : ZMod 3385993424237981517731)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (673, 1), (2689, 1), (28549, 1), (85113533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (673, 1), (2689, 1), (28549, 1), (85113533, 1)] : List FactorBlock).map factorBlockValue).prod) = 3385993424237981517731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_673
      · exact prime_eightyTwoCB_2689
      · exact prime_eightyTwoCB_28549
      · exact prime_eightyTwoCB_85113533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3385993424237981517731) ^ 1692996712118990758865 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 677198684847596303546 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 483713346319711645390 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 307817584021634683430 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 5031193795301607010 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 1259201719686865570 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 118602873103715770 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385993424237981517731) ^ 39782080532810 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6421931631871928113703 : Nat.Prime 6421931631871928113703 := by
  apply lucas_primality 6421931631871928113703 (5 : ZMod 6421931631871928113703)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619, 1), (7621, 1), (680664454275749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619, 1), (7621, 1), (680664454275749, 1)] : List FactorBlock).map factorBlockValue).prod) = 6421931631871928113703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_619
      · exact prime_eightyTwoCB_7621
      · exact prime_eightyTwoCB_680664454275749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6421931631871928113703) ^ 3210965815935964056851 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6421931631871928113703) ^ 10374687612070966258 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6421931631871928113703) ^ 842662594393377262 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 6421931631871928113703) ^ 9434798 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_7024194722597481031763 : Nat.Prime 7024194722597481031763 := by
  apply lucas_primality 7024194722597481031763 (2 : ZMod 7024194722597481031763)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (137, 1), (2269, 1), (69677, 1), (2420177603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (137, 1), (2269, 1), (69677, 1), (2420177603, 1)] : List FactorBlock).map factorBlockValue).prod) = 7024194722597481031763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_137
      · exact prime_eightyTwoCB_2269
      · exact prime_eightyTwoCB_69677
      · exact prime_eightyTwoCB_2420177603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7024194722597481031763) ^ 3512097361298740515881 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7024194722597481031763) ^ 104838727202947478086 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7024194722597481031763) ^ 51271494325529058626 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7024194722597481031763) ^ 3095722663110392698 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7024194722597481031763) ^ 100810808768998106 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 7024194722597481031763) ^ 2902346800454 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_11087189320671416394061 : Nat.Prime 11087189320671416394061 := by
  apply lucas_primality 11087189320671416394061 (10 : ZMod 11087189320671416394061)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11087, 1), (16666951265252723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11087, 1), (16666951265252723, 1)] : List FactorBlock).map factorBlockValue).prod) = 11087189320671416394061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_11087
      · exact prime_eightyTwoCB_16666951265252723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 11087189320671416394061) ^ 5543594660335708197030 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 11087189320671416394061) ^ 3695729773557138798020 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 11087189320671416394061) ^ 2217437864134283278812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 11087189320671416394061) ^ 1000017075915163380 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (10 : ZMod 11087189320671416394061) ^ 665220 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_12408604666631011659199 : Nat.Prime 12408604666631011659199 := by
  apply lucas_primality 12408604666631011659199 (6 : ZMod 12408604666631011659199)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (42206138321874189317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (42206138321874189317, 1)] : List FactorBlock).map factorBlockValue).prod) = 12408604666631011659199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_42206138321874189317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12408604666631011659199) ^ 6204302333315505829599 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 12408604666631011659199) ^ 4136201555543670553066 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 12408604666631011659199) ^ 1772657809518715951314 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 12408604666631011659199) ^ 294 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_15729613182158995211623 : Nat.Prime 15729613182158995211623 := by
  apply lucas_primality 15729613182158995211623 (5 : ZMod 15729613182158995211623)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (1129, 1), (6468124963365167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (1129, 1), (6468124963365167, 1)] : List FactorBlock).map factorBlockValue).prod) = 15729613182158995211623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_359
      · exact prime_eightyTwoCB_1129
      · exact prime_eightyTwoCB_6468124963365167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15729613182158995211623) ^ 7864806591079497605811 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15729613182158995211623) ^ 5243204394052998403874 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15729613182158995211623) ^ 43815078501835641258 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15729613182158995211623) ^ 13932341171088569718 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15729613182158995211623) ^ 2431866 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_20269531290089991493739 : Nat.Prime 20269531290089991493739 := by
  apply lucas_primality 20269531290089991493739 (2 : ZMod 20269531290089991493739)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (73, 1), (2371, 1), (1140569, 1), (60611401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (73, 1), (2371, 1), (1140569, 1), (60611401, 1)] : List FactorBlock).map factorBlockValue).prod) = 20269531290089991493739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_2371
      · exact prime_eightyTwoCB_1140569
      · exact prime_eightyTwoCB_60611401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20269531290089991493739) ^ 10134765645044995746869 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 2895647327155713070534 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 1842684662735453772158 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 277664812193013582106 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 8548937701429772878 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 17771420484065402 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20269531290089991493739) ^ 334417798560538 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_21418417770426224665417 : Nat.Prime 21418417770426224665417 := by
  apply lucas_primality 21418417770426224665417 (7 : ZMod 21418417770426224665417)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (67, 1), (313, 1), (6793, 1), (113891, 1), (1410397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (67, 1), (313, 1), (6793, 1), (113891, 1), (1410397, 1)] : List FactorBlock).map factorBlockValue).prod) = 21418417770426224665417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_313
      · exact prime_eightyTwoCB_6793
      · exact prime_eightyTwoCB_113891
      · exact prime_eightyTwoCB_1410397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21418417770426224665417) ^ 10709208885213112332708 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 7139472590142074888472 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 1647570597725094205032 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 319677877170540666648 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 68429449745770685832 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 3153013067926722312 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 188060670030346776 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 21418417770426224665417) ^ 15186091412861928 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_25779640398353286408389 : Nat.Prime 25779640398353286408389 := by
  apply lucas_primality 25779640398353286408389 (3 : ZMod 25779640398353286408389)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (339205794715174821163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (339205794715174821163, 1)] : List FactorBlock).map factorBlockValue).prod) = 25779640398353286408389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_339205794715174821163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25779640398353286408389) ^ 12889820199176643204194 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 25779640398353286408389) ^ 1356823178860699284652 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 25779640398353286408389) ^ 76 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_29390998271157319225843 : Nat.Prime 29390998271157319225843 := by
  apply lucas_primality 29390998271157319225843 (13 : ZMod 29390998271157319225843)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (137, 1), (42359, 1), (40195508403049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (137, 1), (42359, 1), (40195508403049, 1)] : List FactorBlock).map factorBlockValue).prod) = 29390998271157319225843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_137
      · exact prime_eightyTwoCB_42359
      · exact prime_eightyTwoCB_40195508403049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 29390998271157319225843) ^ 14695499135578659612921 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 29390998271157319225843) ^ 9796999423719106408614 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 29390998271157319225843) ^ 4198714038736759889406 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 29390998271157319225843) ^ 214532834096038826466 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 29390998271157319225843) ^ 693854866053431838 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 29390998271157319225843) ^ 731201058 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_38159077757462270203691 : Nat.Prime 38159077757462270203691 := by
  apply lucas_primality 38159077757462270203691 (2 : ZMod 38159077757462270203691)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (62819, 1), (60744484562731451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (62819, 1), (60744484562731451, 1)] : List FactorBlock).map factorBlockValue).prod) = 38159077757462270203691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_62819
      · exact prime_eightyTwoCB_60744484562731451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38159077757462270203691) ^ 19079538878731135101845 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38159077757462270203691) ^ 7631815551492454040738 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38159077757462270203691) ^ 607444845627314510 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38159077757462270203691) ^ 628190 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_52870383527753049507721 : Nat.Prime 52870383527753049507721 := by
  apply lucas_primality 52870383527753049507721 (7 : ZMod 52870383527753049507721)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (167, 1), (367, 1), (798741353619631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (167, 1), (367, 1), (798741353619631, 1)] : List FactorBlock).map factorBlockValue).prod) = 52870383527753049507721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_167
      · exact prime_eightyTwoCB_367
      · exact prime_eightyTwoCB_798741353619631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52870383527753049507721) ^ 26435191763876524753860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52870383527753049507721) ^ 17623461175917683169240 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52870383527753049507721) ^ 10574076705550609901544 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52870383527753049507721) ^ 316589122920676943160 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52870383527753049507721) ^ 144060990538836647160 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 52870383527753049507721) ^ 66192120 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_62918452728635980846493 : Nat.Prime 62918452728635980846493 := by
  apply lucas_primality 62918452728635980846493 (2 : ZMod 62918452728635980846493)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15729613182158995211623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15729613182158995211623, 1)] : List FactorBlock).map factorBlockValue).prod) = 62918452728635980846493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_15729613182158995211623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 62918452728635980846493) ^ 31459226364317990423246 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 62918452728635980846493) ^ 4 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_112834046597878740134233 : Nat.Prime 112834046597878740134233 := by
  apply lucas_primality 112834046597878740134233 (5 : ZMod 112834046597878740134233)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (82481028214823640449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (82481028214823640449, 1)] : List FactorBlock).map factorBlockValue).prod) = 112834046597878740134233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_82481028214823640449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 112834046597878740134233) ^ 56417023298939370067116 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 112834046597878740134233) ^ 37611348865959580044744 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 112834046597878740134233) ^ 5938634031467302112328 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 112834046597878740134233) ^ 1368 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_116318497641653550217567 : Nat.Prime 116318497641653550217567 := by
  apply lucas_primality 116318497641653550217567 (3 : ZMod 116318497641653550217567)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (1289, 1), (6763, 1), (27253, 1), (1383053249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (1289, 1), (6763, 1), (27253, 1), (1383053249, 1)] : List FactorBlock).map factorBlockValue).prod) = 116318497641653550217567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_59
      · exact prime_eightyTwoCB_1289
      · exact prime_eightyTwoCB_6763
      · exact prime_eightyTwoCB_27253
      · exact prime_eightyTwoCB_1383053249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116318497641653550217567) ^ 58159248820826775108783 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 38772832547217850072522 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 1971499960028026274874 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 90239330986542707694 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 17199245548078301082 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 4268098838353706022 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 116318497641653550217567) ^ 84102689267934 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_132970160334162828133993 : Nat.Prime 132970160334162828133993 := by
  apply lucas_primality 132970160334162828133993 (5 : ZMod 132970160334162828133993)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (61, 1), (8831, 1), (10284974776368613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (61, 1), (8831, 1), (10284974776368613, 1)] : List FactorBlock).map factorBlockValue).prod) = 132970160334162828133993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_61
      · exact prime_eightyTwoCB_8831
      · exact prime_eightyTwoCB_10284974776368613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 132970160334162828133993) ^ 66485080167081414066996 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132970160334162828133993) ^ 44323386778054276044664 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132970160334162828133993) ^ 2179838694002669313672 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132970160334162828133993) ^ 15057203072603649432 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132970160334162828133993) ^ 12928584 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_309355684780239436900669 : Nat.Prime 309355684780239436900669 := by
  apply lucas_primality 309355684780239436900669 (6 : ZMod 309355684780239436900669)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (25779640398353286408389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (25779640398353286408389, 1)] : List FactorBlock).map factorBlockValue).prod) = 309355684780239436900669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_25779640398353286408389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 309355684780239436900669) ^ 154677842390119718450334 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 309355684780239436900669) ^ 103118561593413145633556 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 309355684780239436900669) ^ 12 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_394491470957893764515549 : Nat.Prime 394491470957893764515549 := by
  apply lucas_primality 394491470957893764515549 (2 : ZMod 394491470957893764515549)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (155291, 1), (591877210255909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (155291, 1), (591877210255909, 1)] : List FactorBlock).map factorBlockValue).prod) = 394491470957893764515549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_29
      · exact prime_eightyTwoCB_37
      · exact prime_eightyTwoCB_155291
      · exact prime_eightyTwoCB_591877210255909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 394491470957893764515549) ^ 197245735478946882257774 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 394491470957893764515549) ^ 13603154170961853948812 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 394491470957893764515549) ^ 10661931647510642284204 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 394491470957893764515549) ^ 2540336986418361428 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 394491470957893764515549) ^ 666508972 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_629645477313169759730411 : Nat.Prime 629645477313169759730411 := by
  apply lucas_primality 629645477313169759730411 (2 : ZMod 629645477313169759730411)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1987, 1), (773291221, 1), (40978413583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1987, 1), (773291221, 1), (40978413583, 1)] : List FactorBlock).map factorBlockValue).prod) = 629645477313169759730411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_1987
      · exact prime_eightyTwoCB_773291221
      · exact prime_eightyTwoCB_40978413583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 629645477313169759730411) ^ 314822738656584879865205 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 629645477313169759730411) ^ 125929095462633951946082 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 629645477313169759730411) ^ 316882474742410548430 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 629645477313169759730411) ^ 814241077894210 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 629645477313169759730411) ^ 15365296561270 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_792954993059254817526167 : Nat.Prime 792954993059254817526167 := by
  apply lucas_primality 792954993059254817526167 (5 : ZMod 792954993059254817526167)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2687, 1), (147553962236556534709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2687, 1), (147553962236556534709, 1)] : List FactorBlock).map factorBlockValue).prod) = 792954993059254817526167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_2687
      · exact prime_eightyTwoCB_147553962236556534709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 792954993059254817526167) ^ 396477496529627408763083 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 792954993059254817526167) ^ 295107924473113069418 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 792954993059254817526167) ^ 5374 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_1185389373183403046267383 : Nat.Prime 1185389373183403046267383 := by
  apply lucas_primality 1185389373183403046267383 (3 : ZMod 1185389373183403046267383)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (2948729784038316035491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (2948729784038316035491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185389373183403046267383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_67
      · exact prime_eightyTwoCB_2948729784038316035491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1185389373183403046267383) ^ 592694686591701523133691 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185389373183403046267383) ^ 395129791061134348755794 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185389373183403046267383) ^ 17692378704229896212946 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185389373183403046267383) ^ 402 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2262870185715686353016471 : Nat.Prime 2262870185715686353016471 := by
  apply lucas_primality 2262870185715686353016471 (7 : ZMod 2262870185715686353016471)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (43, 1), (1303807, 1), (310480639447519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (43, 1), (1303807, 1), (310480639447519, 1)] : List FactorBlock).map factorBlockValue).prod) = 2262870185715686353016471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_13
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_1303807
      · exact prime_eightyTwoCB_310480639447519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2262870185715686353016471) ^ 1131435092857843176508235 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2262870185715686353016471) ^ 452574037143137270603294 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2262870185715686353016471) ^ 174066937362745104078190 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2262870185715686353016471) ^ 52624888039899682628290 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2262870185715686353016471) ^ 1735586774511631210 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2262870185715686353016471) ^ 7288281130 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_2925343527351582218947847 : Nat.Prime 2925343527351582218947847 := by
  apply lucas_primality 2925343527351582218947847 (5 : ZMod 2925343527351582218947847)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (132970160334162828133993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (132970160334162828133993, 1)] : List FactorBlock).map factorBlockValue).prod) = 2925343527351582218947847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_11
      · exact prime_eightyTwoCB_132970160334162828133993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2925343527351582218947847) ^ 1462671763675791109473923 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2925343527351582218947847) ^ 265940320668325656267986 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2925343527351582218947847) ^ 22 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_4018149148109231762586797 : Nat.Prime 4018149148109231762586797 := by
  apply lucas_primality 4018149148109231762586797 (2 : ZMod 4018149148109231762586797)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (52870383527753049507721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (52870383527753049507721, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018149148109231762586797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_19
      · exact prime_eightyTwoCB_52870383527753049507721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4018149148109231762586797) ^ 2009074574054615881293398 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4018149148109231762586797) ^ 211481534111012198030884 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4018149148109231762586797) ^ 76 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_6492926427997551050561359 : Nat.Prime 6492926427997551050561359 := by
  apply lucas_primality 6492926427997551050561359 (6 : ZMod 6492926427997551050561359)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (89, 1), (296561908650660046157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (89, 1), (296561908650660046157, 1)] : List FactorBlock).map factorBlockValue).prod) = 6492926427997551050561359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_41
      · exact prime_eightyTwoCB_89
      · exact prime_eightyTwoCB_296561908650660046157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6492926427997551050561359) ^ 3246463213998775525280679 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6492926427997551050561359) ^ 2164308809332517016853786 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6492926427997551050561359) ^ 158364059219452464647838 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6492926427997551050561359) ^ 72954229528062371354622 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (6 : ZMod 6492926427997551050561359) ^ 21894 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_10116444171598814018150021 : Nat.Prime 10116444171598814018150021 := by
  apply lucas_primality 10116444171598814018150021 (2 : ZMod 10116444171598814018150021)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (109, 1), (163, 1), (1063, 1), (35969, 1), (106371215707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (109, 1), (163, 1), (1063, 1), (35969, 1), (106371215707, 1)] : List FactorBlock).map factorBlockValue).prod) = 10116444171598814018150021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_109
      · exact prime_eightyTwoCB_163
      · exact prime_eightyTwoCB_1063
      · exact prime_eightyTwoCB_35969
      · exact prime_eightyTwoCB_106371215707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10116444171598814018150021) ^ 5058222085799407009075010 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 2023288834319762803630004 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 1445206310228402002592860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 92811414418337743285780 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 62064074672385362074540 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 9516880688239712152540 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 281254529500370152580 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 10116444171598814018150021) ^ 95105091206860 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_14088923775095398159559897 : Nat.Prime 14088923775095398159559897 := by
  apply lucas_primality 14088923775095398159559897 (3 : ZMod 14088923775095398159559897)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (47, 1), (103423, 1), (8425668878709889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (47, 1), (103423, 1), (8425668878709889, 1)] : List FactorBlock).map factorBlockValue).prod) = 14088923775095398159559897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_43
      · exact prime_eightyTwoCB_47
      · exact prime_eightyTwoCB_103423
      · exact prime_eightyTwoCB_8425668878709889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14088923775095398159559897) ^ 7044461887547699079779948 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14088923775095398159559897) ^ 327649390118497631617672 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14088923775095398159559897) ^ 299764335640327620416168 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14088923775095398159559897) ^ 136226214430981485352 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14088923775095398159559897) ^ 1672143064 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_47898164276893001351744887 : Nat.Prime 47898164276893001351744887 := by
  apply lucas_primality 47898164276893001351744887 (3 : ZMod 47898164276893001351744887)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (101, 1), (1681699469029316808923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (101, 1), (1681699469029316808923, 1)] : List FactorBlock).map factorBlockValue).prod) = 47898164276893001351744887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_47
      · exact prime_eightyTwoCB_101
      · exact prime_eightyTwoCB_1681699469029316808923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47898164276893001351744887) ^ 23949082138446500675872443 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47898164276893001351744887) ^ 15966054758964333783914962 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47898164276893001351744887) ^ 1019109878231765986207338 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47898164276893001351744887) ^ 474239250266267340116286 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 47898164276893001351744887) ^ 28482 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_58506870547031644378956941 : Nat.Prime 58506870547031644378956941 := by
  apply lucas_primality 58506870547031644378956941 (2 : ZMod 58506870547031644378956941)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2925343527351582218947847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2925343527351582218947847, 1)] : List FactorBlock).map factorBlockValue).prod) = 58506870547031644378956941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_2925343527351582218947847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58506870547031644378956941) ^ 29253435273515822189478470 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 58506870547031644378956941) ^ 11701374109406328875791388 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 58506870547031644378956941) ^ 20 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_127225570205290596766314503 : Nat.Prime 127225570205290596766314503 := by
  apply lucas_primality 127225570205290596766314503 (5 : ZMod 127225570205290596766314503)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18803, 1), (78297061, 1), (43208760066397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18803, 1), (78297061, 1), (43208760066397, 1)] : List FactorBlock).map factorBlockValue).prod) = 127225570205290596766314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_18803
      · exact prime_eightyTwoCB_78297061
      · exact prime_eightyTwoCB_43208760066397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 127225570205290596766314503) ^ 63612785102645298383157251 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 127225570205290596766314503) ^ 6766237845306099918434 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 127225570205290596766314503) ^ 1624908631056925582 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (5 : ZMod 127225570205290596766314503) ^ 2944439275966 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_140297951514372553887021203 : Nat.Prime 140297951514372553887021203 := by
  apply lucas_primality 140297951514372553887021203 (2 : ZMod 140297951514372553887021203)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2262870185715686353016471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2262870185715686353016471, 1)] : List FactorBlock).map factorBlockValue).prod) = 140297951514372553887021203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_31
      · exact prime_eightyTwoCB_2262870185715686353016471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140297951514372553887021203) ^ 70148975757186276943510601 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 140297951514372553887021203) ^ 4525740371431372706032942 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 140297951514372553887021203) ^ 62 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_357733891130743301608603879 : Nat.Prime 357733891130743301608603879 := by
  apply lucas_primality 357733891130743301608603879 (3 : ZMod 357733891130743301608603879)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (11321, 1), (74176390614546837343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (11321, 1), (74176390614546837343, 1)] : List FactorBlock).map factorBlockValue).prod) = 357733891130743301608603879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_71
      · exact prime_eightyTwoCB_11321
      · exact prime_eightyTwoCB_74176390614546837343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 357733891130743301608603879) ^ 178866945565371650804301939 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 357733891130743301608603879) ^ 119244630376914433869534626 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 357733891130743301608603879) ^ 5038505508883708473360618 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 357733891130743301608603879) ^ 31599142401796952708118 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 357733891130743301608603879) ^ 4822746 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_398954257186960636773381281 : Nat.Prime 398954257186960636773381281 := by
  apply lucas_primality 398954257186960636773381281 (3 : ZMod 398954257186960636773381281)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (13003, 1), (862957, 1), (31744782992089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (13003, 1), (862957, 1), (31744782992089, 1)] : List FactorBlock).map factorBlockValue).prod) = 398954257186960636773381281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_7
      · exact prime_eightyTwoCB_13003
      · exact prime_eightyTwoCB_862957
      · exact prime_eightyTwoCB_31744782992089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 398954257186960636773381281) ^ 199477128593480318386690640 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 398954257186960636773381281) ^ 79790851437392127354676256 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 398954257186960636773381281) ^ 56993465312422948110483040 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 398954257186960636773381281) ^ 30681708620084644833760 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 398954257186960636773381281) ^ 462310702835669259040 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 398954257186960636773381281) ^ 12567553455520 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_470611089788502110368600249 : Nat.Prime 470611089788502110368600249 := by
  apply lucas_primality 470611089788502110368600249 (13 : ZMod 470611089788502110368600249)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1163, 1), (43711, 1), (3737953, 1), (103192140713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1163, 1), (43711, 1), (3737953, 1), (103192140713, 1)] : List FactorBlock).map factorBlockValue).prod) = 470611089788502110368600249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_1163
      · exact prime_eightyTwoCB_43711
      · exact prime_eightyTwoCB_3737953
      · exact prime_eightyTwoCB_103192140713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 470611089788502110368600249) ^ 235305544894251055184300124 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 470611089788502110368600249) ^ 156870363262834036789533416 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 470611089788502110368600249) ^ 404652699732160026112296 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 470611089788502110368600249) ^ 10766422405996250608968 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 470611089788502110368600249) ^ 125900750969448281016 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (13 : ZMod 470611089788502110368600249) ^ 4560532289928696 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_707634193404609012671033951 : Nat.Prime 707634193404609012671033951 := by
  apply lucas_primality 707634193404609012671033951 (7 : ZMod 707634193404609012671033951)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (79, 1), (149, 1), (6469, 1), (8080913518165127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (79, 1), (149, 1), (6469, 1), (8080913518165127, 1)] : List FactorBlock).map factorBlockValue).prod) = 707634193404609012671033951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5
      · exact prime_eightyTwoCB_23
      · exact prime_eightyTwoCB_79
      · exact prime_eightyTwoCB_149
      · exact prime_eightyTwoCB_6469
      · exact prime_eightyTwoCB_8080913518165127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 707634193404609012671033951) ^ 353817096702304506335516975 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 141526838680921802534206790 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 30766704061069957072653650 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 8957394853222898894570050 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 4749222774527577266248550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 109388497975669966404550 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (7 : ZMod 707634193404609012671033951) ^ 87568588850 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_734438518912359354060088267 : Nat.Prime 734438518912359354060088267 := by
  apply lucas_primality 734438518912359354060088267 (3 : ZMod 734438518912359354060088267)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (523, 1), (175745659, 1), (18242948839751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (523, 1), (175745659, 1), (18242948839751, 1)] : List FactorBlock).map factorBlockValue).prod) = 734438518912359354060088267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_73
      · exact prime_eightyTwoCB_523
      · exact prime_eightyTwoCB_175745659
      · exact prime_eightyTwoCB_18242948839751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 734438518912359354060088267) ^ 367219259456179677030044133 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 734438518912359354060088267) ^ 244812839637453118020029422 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 734438518912359354060088267) ^ 10060801628936429507672442 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 734438518912359354060088267) ^ 1404280150884052302218142 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 734438518912359354060088267) ^ 4178985262517120574 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (3 : ZMod 734438518912359354060088267) ^ 40258761089766 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_9694588449643143473593165123 : Nat.Prime 9694588449643143473593165123 := by
  apply lucas_primality 9694588449643143473593165123 (2 : ZMod 9694588449643143473593165123)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1741, 1), (309355684780239436900669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1741, 1), (309355684780239436900669, 1)] : List FactorBlock).map factorBlockValue).prod) = 9694588449643143473593165123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_3
      · exact prime_eightyTwoCB_1741
      · exact prime_eightyTwoCB_309355684780239436900669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9694588449643143473593165123) ^ 4847294224821571736796582561 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9694588449643143473593165123) ^ 3231529483214381157864388374 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9694588449643143473593165123) ^ 5568402326044309864212042 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9694588449643143473593165123) ^ 31338 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem prime_eightyTwoCB_12118235562053929341991456403 : Nat.Prime 12118235562053929341991456403 := by
  apply lucas_primality 12118235562053929341991456403 (2 : ZMod 12118235562053929341991456403)
  · rw [← eightyTwoCBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5557, 1), (2796566237, 1), (389891608199689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5557, 1), (2796566237, 1), (389891608199689, 1)] : List FactorBlock).map factorBlockValue).prod) = 12118235562053929341991456403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyTwoCB_2
      · exact prime_eightyTwoCB_5557
      · exact prime_eightyTwoCB_2796566237
      · exact prime_eightyTwoCB_389891608199689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12118235562053929341991456403) ^ 6059117781026964670995728201 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12118235562053929341991456403) ^ 2180715415161765222600586 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12118235562053929341991456403) ^ 4333255333531343546 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide
    · change (2 : ZMod 12118235562053929341991456403) ^ 31081037158018 ≠ 1
      rw [← eightyTwoCBFastPow_eq_pow]
      decide

private theorem phi_eightyTwoCB_96945884496431434735931651200 : Nat.totient 96945884496431434735931651200 = 35138533003743346043617280000 := by
  rw [← show ((([(2, 7), (5, 2), (11, 1), (389, 1), (1481, 1), (236231, 1), (20236954983689, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_11, prime_eightyTwoCB_389, prime_eightyTwoCB_1481, prime_eightyTwoCB_236231, prime_eightyTwoCB_20236954983689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651201 : Nat.totient 96945884496431434735931651201 = 83094105476686910982496968528 := by
  rw [← show ((([(7, 1), (35107, 1), (394491470957893764515549, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_7, prime_eightyTwoCB_35107, prime_eightyTwoCB_394491470957893764515549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651202 : Nat.totient 96945884496431434735931651202 = 30760195643443766689807478400 := by
  rw [← show ((([(2, 1), (3, 4), (31, 1), (61, 1), (79020517, 1), (4004819686857343, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_31, prime_eightyTwoCB_61, prime_eightyTwoCB_79020517, prime_eightyTwoCB_4004819686857343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651203 : Nat.totient 96945884496431434735931651203 = 91843446618659054619335075040 := by
  rw [← show ((([(19, 1), (6056959, 1), (11864581, 1), (71001698308003, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_19, prime_eightyTwoCB_6056959, prime_eightyTwoCB_11864581, prime_eightyTwoCB_71001698308003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651204 : Nat.totient 96945884496431434735931651204 = 48472928199826272172996861224 := by
  rw [← show ((([(2, 2), (3450427, 1), (7024194722597481031763, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3450427, prime_eightyTwoCB_7024194722597481031763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651205 : Nat.totient 96945884496431434735931651205 = 51704372462592765477732773568 := by
  rw [← show ((([(3, 1), (5, 1), (520853, 1), (12408604666631011659199, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_520853, prime_eightyTwoCB_12408604666631011659199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651206 : Nat.totient 96945884496431434735931651206 = 47162862723875748505782872256 := by
  rw [← show ((([(2, 1), (37, 1), (11453073257, 1), (114386723181163567, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_37, prime_eightyTwoCB_11453073257, prime_eightyTwoCB_114386723181163567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651207 : Nat.totient 96945884496431434735931651207 = 94845060077244109152208416000 := by
  rw [← show ((([(59, 1), (211, 1), (15803, 1), (5729860141, 1), (86002554041, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_59, prime_eightyTwoCB_211, prime_eightyTwoCB_15803, prime_eightyTwoCB_5729860141, prime_eightyTwoCB_86002554041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651208 : Nat.totient 96945884496431434735931651208 = 26063542108979841517109194752 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (17, 1), (4423, 1), (574543, 1), (13357700358950837, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_7, prime_eightyTwoCB_17, prime_eightyTwoCB_4423, prime_eightyTwoCB_574543, prime_eightyTwoCB_13357700358950837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651209 : Nat.totient 96945884496431434735931651209 = 96588150605300691434323047060 := by
  rw [← show ((([(271, 1), (357733891130743301608603879, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_271, prime_eightyTwoCB_357733891130743301608603879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651210 : Nat.totient 96945884496431434735931651210 = 38775723839321356146735513600 := by
  rw [← show ((([(2, 1), (5, 1), (15361, 1), (368111, 1), (262105469, 1), (6541163579, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_15361, prime_eightyTwoCB_368111, prime_eightyTwoCB_262105469, prime_eightyTwoCB_6541163579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651211 : Nat.totient 96945884496431434735931651211 = 58755081508006105270512129600 := by
  rw [← show ((([(3, 2), (11, 2), (11791969171, 1), (7549447381204969, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_11, prime_eightyTwoCB_11791969171, prime_eightyTwoCB_7549447381204969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651212 : Nat.totient 96945884496431434735931651212 = 44744254382965938044225702400 := by
  rw [← show ((([(2, 2), (13, 1), (24457507595791, 1), (76227879121441, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_13, prime_eightyTwoCB_24457507595791, prime_eightyTwoCB_76227879121441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651213 : Nat.totient 96945884496431434735931651213 = 94691298737765298721011659520 := by
  rw [← show ((([(43, 1), (3127781, 1), (3097499147, 1), (232709112113, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_43, prime_eightyTwoCB_3127781, prime_eightyTwoCB_3097499147, prime_eightyTwoCB_232709112113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651214 : Nat.totient 96945884496431434735931651214 = 32315273443479034373083699392 := by
  rw [← show ((([(2, 1), (3, 1), (1513417, 1), (894577063, 1), (11934432164339, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_1513417, prime_eightyTwoCB_894577063, prime_eightyTwoCB_11934432164339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651215 : Nat.totient 96945884496431434735931651215 = 66476747302277208731851419648 := by
  rw [← show ((([(5, 1), (7, 2), (154369, 1), (2563322219749667798003, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_7, prime_eightyTwoCB_154369, prime_eightyTwoCB_2563322219749667798003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651216 : Nat.totient 96945884496431434735931651216 = 48464219369225043804039588864 := by
  rw [← show ((([(2, 4), (5557, 1), (2796566237, 1), (389891608199689, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5557, prime_eightyTwoCB_2796566237, prime_eightyTwoCB_389891608199689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651217 : Nat.totient 96945884496431434735931651217 = 64587238387457344608895502400 := by
  rw [← show ((([(3, 1), (1571, 1), (40087, 1), (108023, 1), (34050019, 1), (139506611, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_1571, prime_eightyTwoCB_40087, prime_eightyTwoCB_108023, prime_eightyTwoCB_34050019, prime_eightyTwoCB_139506611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651218 : Nat.totient 96945884496431434735931651218 = 48288439764710376176047631760 := by
  rw [← show ((([(2, 1), (263, 1), (250867, 1), (21641311, 1), (33948182692939, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_263, prime_eightyTwoCB_250867, prime_eightyTwoCB_21641311, prime_eightyTwoCB_33948182692939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651219 : Nat.totient 96945884496431434735931651219 = 92642446758806447518201168576 := by
  rw [← show ((([(23, 1), (1049, 1), (4018149148109231762586797, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_23, prime_eightyTwoCB_1049, prime_eightyTwoCB_4018149148109231762586797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651220 : Nat.totient 96945884496431434735931651220 = 25837386792845597769943791360 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (1741, 1), (309355684780239436900669, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_1741, prime_eightyTwoCB_309355684780239436900669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651221 : Nat.totient 96945884496431434735931651221 = 96945883897548837321426279360 := by
  rw [← show ((([(168611669, 1), (4176368741, 1), (137671141549, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_168611669, prime_eightyTwoCB_4176368741, prime_eightyTwoCB_137671141549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651222 : Nat.totient 96945884496431434735931651222 = 34238378113908606401823360000 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (19, 1), (41, 1), (71, 1), (191, 1), (257459, 1), (231457578257183, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_7, prime_eightyTwoCB_11, prime_eightyTwoCB_19, prime_eightyTwoCB_41, prime_eightyTwoCB_71, prime_eightyTwoCB_191, prime_eightyTwoCB_257459, prime_eightyTwoCB_231457578257183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651223 : Nat.totient 96945884496431434735931651223 = 64630587327798365097055284600 := by
  rw [← show ((([(3, 1), (27661411, 1), (1168244629030088580031, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_27661411, prime_eightyTwoCB_1168244629030088580031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651224 : Nat.totient 96945884496431434735931651224 = 48472942248215717367965825608 := by
  rw [← show ((([(2, 3), (12118235562053929341991456403, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_12118235562053929341991456403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651225 : Nat.totient 96945884496431434735931651225 = 67370827392137983748774952960 := by
  rw [← show ((([(5, 2), (13, 1), (17, 1), (11177, 1), (26449, 1), (374359, 1), (158552943467, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_13, prime_eightyTwoCB_17, prime_eightyTwoCB_11177, prime_eightyTwoCB_26449, prime_eightyTwoCB_374359, prime_eightyTwoCB_158552943467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651226 : Nat.totient 96945884496431434735931651226 = 32151231727432331204787215616 := by
  rw [← show ((([(2, 1), (3, 1), (197, 1), (2279749, 1), (2685509, 1), (13396713037723, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_197, prime_eightyTwoCB_2279749, prime_eightyTwoCB_2685509, prime_eightyTwoCB_13396713037723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651227 : Nat.totient 96945884496431434735931651227 = 92640896806660208716961597472 := by
  rw [← show ((([(29, 1), (107, 1), (1063, 1), (29390998271157319225843, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_29, prime_eightyTwoCB_107, prime_eightyTwoCB_1063, prime_eightyTwoCB_29390998271157319225843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651228 : Nat.totient 96945884496431434735931651228 = 47749452689053779192925110000 := by
  rw [← show ((([(2, 2), (67, 1), (3727751, 1), (97039307342868248971, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_67, prime_eightyTwoCB_3727751, prime_eightyTwoCB_97039307342868248971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651229 : Nat.totient 96945884496431434735931651229 = 54696412229451370049928879792 := by
  rw [← show ((([(3, 3), (7, 1), (79, 1), (6492926427997551050561359, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_7, prime_eightyTwoCB_79, prime_eightyTwoCB_6492926427997551050561359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651230 : Nat.totient 96945884496431434735931651230 = 38778353798572573894372660488 := by
  rw [← show ((([(2, 1), (5, 1), (9694588449643143473593165123, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_9694588449643143473593165123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651231 : Nat.totient 96945884496431434735931651231 = 96945805071177284526331749120 := by
  rw [← show ((([(1220833, 1), (6203867587, 1), (12800018503061, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_1220833, prime_eightyTwoCB_6203867587, prime_eightyTwoCB_12800018503061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651232 : Nat.totient 96945884496431434735931651232 = 32315294819790476981689635072 := by
  rw [← show ((([(2, 5), (3, 1), (2615916763, 1), (386041703538903509, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_2615916763, prime_eightyTwoCB_386041703538903509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651233 : Nat.totient 96945884496431434735931651233 = 85289599171016036716180856400 := by
  rw [← show ((([(11, 1), (31, 1), (2417279, 1), (117611074896386261347, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_11, prime_eightyTwoCB_31, prime_eightyTwoCB_2417279, prime_eightyTwoCB_117611074896386261347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651234 : Nat.totient 96945884496431434735931651234 = 48472942246042413935338873956 := by
  rw [← show ((([(2, 1), (22303808119, 1), (2173303410323143543, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_22303808119, prime_eightyTwoCB_2173303410323143543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651235 : Nat.totient 96945884496431434735931651235 = 51515073244936530964961952768 := by
  rw [← show ((([(3, 1), (5, 1), (283, 1), (8389, 1), (92723, 1), (29359862262460649, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_283, prime_eightyTwoCB_8389, prime_eightyTwoCB_92723, prime_eightyTwoCB_29359862262460649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651236 : Nat.totient 96945884496431434735931651236 = 40996218980725194152291719680 := by
  rw [← show ((([(2, 2), (7, 1), (131, 1), (199, 1), (2887, 1), (3517, 1), (22859, 1), (572229962443, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_7, prime_eightyTwoCB_131, prime_eightyTwoCB_199, prime_eightyTwoCB_2887, prime_eightyTwoCB_3517, prime_eightyTwoCB_22859, prime_eightyTwoCB_572229962443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651237 : Nat.totient 96945884496431434735931651237 = 96887377625884403091552692640 := by
  rw [← show ((([(1657, 1), (58506870547031644378956941, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_1657, prime_eightyTwoCB_58506870547031644378956941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651238 : Nat.totient 96945884496431434735931651238 = 29181729395829557139749259264 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (47, 1), (2273, 1), (112643, 1), (34428017719943779, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_13, prime_eightyTwoCB_47, prime_eightyTwoCB_2273, prime_eightyTwoCB_112643, prime_eightyTwoCB_34428017719943779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651239 : Nat.totient 96945884496431434735931651239 = 96945884053018625831180311624 := by
  rw [← show ((([(218635733, 1), (443412808904532703883, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_218635733, prime_eightyTwoCB_443412808904532703883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651240 : Nat.totient 96945884496431434735931651240 = 38778353676506463538093085952 := by
  rw [← show ((([(2, 3), (5, 1), (436314379, 1), (2067700573, 1), (2686471343, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_436314379, prime_eightyTwoCB_2067700573, prime_eightyTwoCB_2686471343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651241 : Nat.totient 96945884496431434735931651241 = 61228911814072736944066789968 := by
  rw [← show ((([(3, 1), (19, 1), (902179, 1), (1885218998852183177947, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_19, prime_eightyTwoCB_902179, prime_eightyTwoCB_1885218998852183177947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651242 : Nat.totient 96945884496431434735931651242 = 43637708158360619604583772160 := by
  rw [← show ((([(2, 1), (17, 1), (23, 1), (129671, 1), (85898929, 1), (11129919294709, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_17, prime_eightyTwoCB_23, prime_eightyTwoCB_129671, prime_eightyTwoCB_85898929, prime_eightyTwoCB_11129919294709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651243 : Nat.totient 96945884496431434735931651243 = 80850621819417721633054959840 := by
  rw [← show ((([(7, 1), (37, 2), (10116444171598814018150021, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_7, prime_eightyTwoCB_37, prime_eightyTwoCB_10116444171598814018150021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651244 : Nat.totient 96945884496431434735931651244 = 29377540756494374162403530640 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (734438518912359354060088267, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_11, prime_eightyTwoCB_734438518912359354060088267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651245 : Nat.totient 96945884496431434735931651245 = 77550595667127416037797838336 := by
  rw [← show ((([(5, 1), (13469, 1), (225427, 1), (7955417, 1), (802703468519, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_13469, prime_eightyTwoCB_225427, prime_eightyTwoCB_7955417, prime_eightyTwoCB_802703468519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651246 : Nat.totient 96945884496431434735931651246 = 48319191523607689296697680000 := by
  rw [← show ((([(2, 1), (631, 1), (811, 1), (2801, 1), (33817076456151626003, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_631, prime_eightyTwoCB_811, prime_eightyTwoCB_2801, prime_eightyTwoCB_33817076456151626003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651247 : Nat.totient 96945884496431434735931651247 = 64630579769926367133326504400 := by
  rw [← show ((([(3, 2), (6915043, 1), (117943171, 1), (13207456314911, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_6915043, prime_eightyTwoCB_117943171, prime_eightyTwoCB_13207456314911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651248 : Nat.totient 96945884496431434735931651248 = 48424979763924720230506752000 := by
  rw [← show ((([(2, 4), (1327, 1), (4391, 1), (120349, 1), (79361641, 1), (108873431, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_1327, prime_eightyTwoCB_4391, prime_eightyTwoCB_120349, prime_eightyTwoCB_79361641, prime_eightyTwoCB_108873431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651249 : Nat.totient 96945884496431434735931651249 = 96748870994141258730131610624 := by
  rw [← show ((([(617, 1), (3779, 1), (6863, 1), (545449, 1), (11107061398789, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_617, prime_eightyTwoCB_3779, prime_eightyTwoCB_6863, prime_eightyTwoCB_545449, prime_eightyTwoCB_11107061398789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651250 : Nat.totient 96945884496431434735931651250 = 21489016112154387022786560000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 4), (7, 1), (53, 1), (89, 1), (2843, 1), (398477, 1), (739253, 1), (934891, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_7, prime_eightyTwoCB_53, prime_eightyTwoCB_89, prime_eightyTwoCB_2843, prime_eightyTwoCB_398477, prime_eightyTwoCB_739253, prime_eightyTwoCB_934891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651251 : Nat.totient 96945884496431434735931651251 = 89247418949735207362784378880 := by
  rw [← show ((([(13, 1), (449, 1), (2137, 1), (84148661, 1), (92360856598939, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_13, prime_eightyTwoCB_449, prime_eightyTwoCB_2137, prime_eightyTwoCB_84148661, prime_eightyTwoCB_92360856598939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651252 : Nat.totient 96945884496431434735931651252 = 48019993995234640220646755040 := by
  rw [← show ((([(2, 2), (109, 1), (5827, 1), (38159077757462270203691, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_109, prime_eightyTwoCB_5827, prime_eightyTwoCB_38159077757462270203691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651253 : Nat.totient 96945884496431434735931651253 = 63721863242241717136402699760 := by
  rw [← show ((([(3, 1), (83, 1), (491, 1), (792954993059254817526167, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_83, prime_eightyTwoCB_491, prime_eightyTwoCB_792954993059254817526167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651254 : Nat.totient 96945884496431434735931651254 = 48467641569804580857731006208 := by
  rw [← show ((([(2, 1), (9277, 1), (847787, 1), (2628089, 1), (2345119639757, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_9277, prime_eightyTwoCB_847787, prime_eightyTwoCB_2628089, prime_eightyTwoCB_2345119639757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651255 : Nat.totient 96945884496431434735931651255 = 70505654328013671133106352000 := by
  rw [← show ((([(5, 1), (11, 1), (158981, 1), (11087189320671416394061, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_11, prime_eightyTwoCB_158981, prime_eightyTwoCB_11087189320671416394061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651256 : Nat.totient 96945884496431434735931651256 = 30475342792303521231071232000 := by
  rw [← show ((([(2, 3), (3, 3), (29, 1), (43, 1), (1559731, 1), (3840601, 1), (60084199313, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_29, prime_eightyTwoCB_43, prime_eightyTwoCB_1559731, prime_eightyTwoCB_3840601, prime_eightyTwoCB_60084199313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651257 : Nat.totient 96945884496431434735931651257 = 83011938882862085956126907232 := by
  rw [← show ((([(7, 1), (983, 1), (14088923775095398159559897, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_7, prime_eightyTwoCB_983, prime_eightyTwoCB_14088923775095398159559897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651258 : Nat.totient 96945884496431434735931651258 = 47808929340699032892535269120 := by
  rw [← show ((([(2, 1), (73, 1), (7544501172781, 1), (88012831107433, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_73, prime_eightyTwoCB_7544501172781, prime_eightyTwoCB_88012831107433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651259 : Nat.totient 96945884496431434735931651259 = 60808641616996682715724076160 := by
  rw [← show ((([(3, 1), (17, 1), (3019, 1), (629645477313169759730411, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_17, prime_eightyTwoCB_3019, prime_eightyTwoCB_629645477313169759730411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651260 : Nat.totient 96945884496431434735931651260 = 36737387809027192164453192000 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (250273149251, 1), (1019369234927227, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_19, prime_eightyTwoCB_250273149251, prime_eightyTwoCB_1019369234927227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651261 : Nat.totient 96945884496431434735931651261 = 96945884481116019042097910172 := by
  rw [← show ((([(6329954503, 1), (15315415687503786587, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_6329954503, prime_eightyTwoCB_15315415687503786587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651262 : Nat.totient 96945884496431434735931651262 = 32315251995308270726193044160 := by
  rw [← show ((([(2, 1), (3, 1), (754381, 1), (21418417770426224665417, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_754381, prime_eightyTwoCB_21418417770426224665417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651263 : Nat.totient 96945884496431434735931651263 = 93030836776294160497834771200 := by
  rw [← show ((([(41, 1), (61, 1), (16710428797, 1), (2319680071050479, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_41, prime_eightyTwoCB_61, prime_eightyTwoCB_16710428797, prime_eightyTwoCB_2319680071050479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651264 : Nat.totient 96945884496431434735931651264 = 37112877596939077144484904960 := by
  rw [← show ((([(2, 6), (7, 2), (13, 1), (31, 1), (23813, 1), (60493, 1), (53251156286737, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_7, prime_eightyTwoCB_13, prime_eightyTwoCB_31, prime_eightyTwoCB_23813, prime_eightyTwoCB_60493, prime_eightyTwoCB_53251156286737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651265 : Nat.totient 96945884496431434735931651265 = 49456060183429586677704130560 := by
  rw [← show ((([(3, 2), (5, 1), (23, 1), (211927, 1), (535793, 1), (757109, 1), (1089550321, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_23, prime_eightyTwoCB_211927, prime_eightyTwoCB_535793, prime_eightyTwoCB_757109, prime_eightyTwoCB_1089550321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651266 : Nat.totient 96945884496431434735931651266 = 43314804246187411337390876160 := by
  rw [← show ((([(2, 1), (11, 1), (59, 1), (10253, 1), (115763, 1), (2058919, 1), (30562909337, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_11, prime_eightyTwoCB_59, prime_eightyTwoCB_10253, prime_eightyTwoCB_115763, prime_eightyTwoCB_2058919, prime_eightyTwoCB_30562909337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651267 : Nat.totient 96945884496431434735931651267 = 96573694601914459581712867200 := by
  rw [← show ((([(439, 1), (643, 1), (103991, 1), (3302616373353997681, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_439, prime_eightyTwoCB_643, prime_eightyTwoCB_103991, prime_eightyTwoCB_3302616373353997681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651268 : Nat.totient 96945884496431434735931651268 = 32315294632757035963432806720 := by
  rw [← show ((([(2, 2), (3, 1), (162073411, 1), (49846693903640695849, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_162073411, prime_eightyTwoCB_49846693903640695849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651269 : Nat.totient 96945884496431434735931651269 = 96631862580250090196758012800 := by
  rw [← show ((([(313, 1), (22853, 1), (1557131, 1), (8703955645749691, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_313, prime_eightyTwoCB_22853, prime_eightyTwoCB_1557131, prime_eightyTwoCB_8703955645749691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651270 : Nat.totient 96945884496431434735931651270 = 38453843080557074637746265600 := by
  rw [← show ((([(2, 1), (5, 1), (151, 1), (569, 1), (112834046597878740134233, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_151, prime_eightyTwoCB_569, prime_eightyTwoCB_112834046597878740134233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651271 : Nat.totient 96945884496431434735931651271 = 55397577960138750763452246144 := by
  rw [← show ((([(3, 1), (7, 1), (1054813, 1), (3111419, 1), (1406617802265733, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_7, prime_eightyTwoCB_1054813, prime_eightyTwoCB_3111419, prime_eightyTwoCB_1406617802265733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651272 : Nat.totient 96945884496431434735931651272 = 48468200690722983755780715216 := by
  rw [← show ((([(2, 3), (10223, 1), (1185389373183403046267383, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_10223, prime_eightyTwoCB_1185389373183403046267383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651273 : Nat.totient 96945884496431434735931651273 = 96805586544917062182044629380 := by
  rw [← show ((([(691, 1), (140297951514372553887021203, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_691, prime_eightyTwoCB_140297951514372553887021203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651274 : Nat.totient 96945884496431434735931651274 = 32314917321427439762758291200 := by
  rw [← show ((([(2, 1), (3, 2), (85601, 1), (62918452728635980846493, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_85601, prime_eightyTwoCB_62918452728635980846493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651275 : Nat.totient 96945884496431434735931651275 = 77488810778161588682074936320 := by
  rw [← show ((([(5, 2), (2153, 1), (2879, 1), (21767, 1), (55837, 1), (514734194687, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_2153, prime_eightyTwoCB_2879, prime_eightyTwoCB_21767, prime_eightyTwoCB_55837, prime_eightyTwoCB_514734194687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651276 : Nat.totient 96945884496431434735931651276 = 45621592704187054738287683072 := by
  rw [← show ((([(2, 2), (17, 1), (2872634247929, 1), (496295263845083, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_17, prime_eightyTwoCB_2872634247929, prime_eightyTwoCB_496295263845083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651277 : Nat.totient 96945884496431434735931651277 = 53902726974020420523745286400 := by
  rw [← show ((([(3, 1), (11, 1), (13, 2), (163, 1), (35000601107, 1), (3046952089261, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_11, prime_eightyTwoCB_13, prime_eightyTwoCB_163, prime_eightyTwoCB_35000601107, prime_eightyTwoCB_3046952089261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651278 : Nat.totient 96945884496431434735931651278 = 41535931725570359195335224864 := by
  rw [← show ((([(2, 1), (7, 1), (4099, 1), (19157, 1), (88185244649680905439, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_7, prime_eightyTwoCB_4099, prime_eightyTwoCB_19157, prime_eightyTwoCB_88185244649680905439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651279 : Nat.totient 96945884496431434735931651279 = 90859874013910663901826269184 := by
  rw [← show ((([(19, 1), (97, 1), (2473, 1), (20273365109, 1), (1049189858329, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_19, prime_eightyTwoCB_97, prime_eightyTwoCB_2473, prime_eightyTwoCB_20273365109, prime_eightyTwoCB_1049189858329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651280 : Nat.totient 96945884496431434735931651280 = 25152529285299212390337527808 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (37, 1), (25219, 1), (253719413, 1), (1706219306873, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_37, prime_eightyTwoCB_25219, prime_eightyTwoCB_253719413, prime_eightyTwoCB_1706219306873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651281 : Nat.totient 96945884496431434735931651281 = 96945876210943383116346643680 := by
  rw [← show ((([(12930571, 1), (123016939, 1), (60946217565049, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_12930571, prime_eightyTwoCB_123016939, prime_eightyTwoCB_60946217565049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651282 : Nat.totient 96945884496431434735931651282 = 48041707970019052798934158272 := by
  rw [← show ((([(2, 1), (113, 1), (21163, 1), (20269531290089991493739, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_113, prime_eightyTwoCB_21163, prime_eightyTwoCB_20269531290089991493739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651283 : Nat.totient 96945884496431434735931651283 = 64630589664287623157287767360 := by
  rw [← show ((([(3, 5), (398954257186960636773381281, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_398954257186960636773381281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651284 : Nat.totient 96945884496431434735931651284 = 47969748427417924109724218400 := by
  rw [← show ((([(2, 2), (101, 1), (2063, 1), (116318497641653550217567, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_101, prime_eightyTwoCB_2063, prime_eightyTwoCB_116318497641653550217567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651285 : Nat.totient 96945884496431434735931651285 = 62804455541404467143273889792 := by
  rw [← show ((([(5, 1), (7, 1), (29, 1), (47, 1), (4253, 1), (477826348840075647809, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_5, prime_eightyTwoCB_7, prime_eightyTwoCB_29, prime_eightyTwoCB_47, prime_eightyTwoCB_4253, prime_eightyTwoCB_477826348840075647809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651286 : Nat.totient 96945884496431434735931651286 = 32060843691733230385111254504 := by
  rw [← show ((([(2, 1), (3, 1), (127, 1), (127225570205290596766314503, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_127, prime_eightyTwoCB_127225570205290596766314503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651287 : Nat.totient 96945884496431434735931651287 = 96238250303026825723260617200 := by
  rw [← show ((([(137, 1), (707634193404609012671033951, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_137, prime_eightyTwoCB_707634193404609012671033951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651288 : Nat.totient 96945884496431434735931651288 = 42150384563665841189535499680 := by
  rw [← show ((([(2, 3), (11, 1), (23, 1), (47898164276893001351744887, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_11, prime_eightyTwoCB_23, prime_eightyTwoCB_47898164276893001351744887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651289 : Nat.totient 96945884496431434735931651289 = 64525925022551374472880588288 := by
  rw [← show ((([(3, 1), (673, 1), (7477, 1), (6421931631871928113703, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_673, prime_eightyTwoCB_7477, prime_eightyTwoCB_6421931631871928113703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651290 : Nat.totient 96945884496431434735931651290 = 35776735434037721334435840000 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (2017, 1), (38839, 1), (979326091, 1), (9720414001, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_13, prime_eightyTwoCB_2017, prime_eightyTwoCB_38839, prime_eightyTwoCB_979326091, prime_eightyTwoCB_9720414001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651291 : Nat.totient 96945884496431434735931651291 = 96850162544434949284874173792 := by
  rw [← show ((([(1013, 1), (4796843, 1), (19950988930779576749, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_1013, prime_eightyTwoCB_4796843, prime_eightyTwoCB_19950988930779576749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651292 : Nat.totient 96945884496431434735931651292 = 27698811768773882830802484864 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (2242363, 1), (1362594839, 1), (125908827053, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_7, prime_eightyTwoCB_2242363, prime_eightyTwoCB_1362594839, prime_eightyTwoCB_125908827053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651293 : Nat.totient 96945884496431434735931651293 = 89958058382948614361479271680 := by
  rw [← show ((([(17, 1), (71, 1), (7663823, 1), (10480370627707108613, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_17, prime_eightyTwoCB_71, prime_eightyTwoCB_7663823, prime_eightyTwoCB_10480370627707108613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651294 : Nat.totient 96945884496431434735931651294 = 48002331158427215257597225296 := by
  rw [← show ((([(2, 1), (103, 1), (470611089788502110368600249, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_103, prime_eightyTwoCB_470611089788502110368600249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651295 : Nat.totient 96945884496431434735931651295 = 49236136701055397807094057600 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (67, 1), (919, 1), (3385993424237981517731, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_5, prime_eightyTwoCB_31, prime_eightyTwoCB_67, prime_eightyTwoCB_919, prime_eightyTwoCB_3385993424237981517731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651296 : Nat.totient 96945884496431434735931651296 = 48469257862672236244729989120 := by
  rw [← show ((([(2, 5), (13219, 1), (2774257, 1), (82610282233036541, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_13219, prime_eightyTwoCB_2774257, prime_eightyTwoCB_82610282233036541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651297 : Nat.totient 96945884496431434735931651297 = 96001487995131167255873808000 := by
  rw [← show ((([(173, 1), (251, 1), (9922247, 1), (225008807892166537, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_173, prime_eightyTwoCB_251, prime_eightyTwoCB_9922247, prime_eightyTwoCB_225008807892166537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651298 : Nat.totient 96945884496431434735931651298 = 30614428931360526018669973824 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (502669, 1), (5423396239, 1), (311940014227, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_3, prime_eightyTwoCB_19, prime_eightyTwoCB_502669, prime_eightyTwoCB_5423396239, prime_eightyTwoCB_311940014227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651299 : Nat.totient 96945884496431434735931651299 = 73290246829310356497946062720 := by
  rw [← show ((([(7, 1), (11, 1), (43, 1), (149, 1), (28726982027, 1), (6840595738283, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_7, prime_eightyTwoCB_11, prime_eightyTwoCB_43, prime_eightyTwoCB_149, prime_eightyTwoCB_28726982027, prime_eightyTwoCB_6840595738283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651300 : Nat.totient 96945884496431434735931651300 = 38778353793226090401344563200 := by
  rw [← show ((([(2, 2), (5, 2), (7253058193, 1), (133662080072644241, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_2, prime_eightyTwoCB_5, prime_eightyTwoCB_7253058193, prime_eightyTwoCB_133662080072644241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyTwoCB_96945884496431434735931651301 : Nat.totient 96945884496431434735931651301 = 64626540129547152192832845312 := by
  rw [← show ((([(3, 2), (20929, 1), (67219, 1), (7656783064031213039, 1)] : List FactorBlock).map factorBlockValue).prod) = 96945884496431434735931651301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyTwoCB_3, prime_eightyTwoCB_20929, prime_eightyTwoCB_67219, prime_eightyTwoCB_7656783064031213039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyTwoCB : certifiedKill 1 96945884496431434735931651199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyTwoCB_96945884496431434735931651200, phi_eightyTwoCB_96945884496431434735931651201, phi_eightyTwoCB_96945884496431434735931651202,
    phi_eightyTwoCB_96945884496431434735931651203, phi_eightyTwoCB_96945884496431434735931651204, phi_eightyTwoCB_96945884496431434735931651205,
    phi_eightyTwoCB_96945884496431434735931651206, phi_eightyTwoCB_96945884496431434735931651207, phi_eightyTwoCB_96945884496431434735931651208,
    phi_eightyTwoCB_96945884496431434735931651209, phi_eightyTwoCB_96945884496431434735931651210, phi_eightyTwoCB_96945884496431434735931651211,
    phi_eightyTwoCB_96945884496431434735931651212, phi_eightyTwoCB_96945884496431434735931651213, phi_eightyTwoCB_96945884496431434735931651214,
    phi_eightyTwoCB_96945884496431434735931651215, phi_eightyTwoCB_96945884496431434735931651216, phi_eightyTwoCB_96945884496431434735931651217,
    phi_eightyTwoCB_96945884496431434735931651218, phi_eightyTwoCB_96945884496431434735931651219, phi_eightyTwoCB_96945884496431434735931651220,
    phi_eightyTwoCB_96945884496431434735931651221, phi_eightyTwoCB_96945884496431434735931651222, phi_eightyTwoCB_96945884496431434735931651223,
    phi_eightyTwoCB_96945884496431434735931651224, phi_eightyTwoCB_96945884496431434735931651225, phi_eightyTwoCB_96945884496431434735931651226,
    phi_eightyTwoCB_96945884496431434735931651227, phi_eightyTwoCB_96945884496431434735931651228, phi_eightyTwoCB_96945884496431434735931651229,
    phi_eightyTwoCB_96945884496431434735931651230, phi_eightyTwoCB_96945884496431434735931651231, phi_eightyTwoCB_96945884496431434735931651232,
    phi_eightyTwoCB_96945884496431434735931651233, phi_eightyTwoCB_96945884496431434735931651234, phi_eightyTwoCB_96945884496431434735931651235,
    phi_eightyTwoCB_96945884496431434735931651236, phi_eightyTwoCB_96945884496431434735931651237, phi_eightyTwoCB_96945884496431434735931651238,
    phi_eightyTwoCB_96945884496431434735931651239, phi_eightyTwoCB_96945884496431434735931651240, phi_eightyTwoCB_96945884496431434735931651241,
    phi_eightyTwoCB_96945884496431434735931651242, phi_eightyTwoCB_96945884496431434735931651243, phi_eightyTwoCB_96945884496431434735931651244,
    phi_eightyTwoCB_96945884496431434735931651245, phi_eightyTwoCB_96945884496431434735931651246, phi_eightyTwoCB_96945884496431434735931651247,
    phi_eightyTwoCB_96945884496431434735931651248, phi_eightyTwoCB_96945884496431434735931651249, phi_eightyTwoCB_96945884496431434735931651250,
    phi_eightyTwoCB_96945884496431434735931651251, phi_eightyTwoCB_96945884496431434735931651252, phi_eightyTwoCB_96945884496431434735931651253,
    phi_eightyTwoCB_96945884496431434735931651254, phi_eightyTwoCB_96945884496431434735931651255, phi_eightyTwoCB_96945884496431434735931651256,
    phi_eightyTwoCB_96945884496431434735931651257, phi_eightyTwoCB_96945884496431434735931651258, phi_eightyTwoCB_96945884496431434735931651259,
    phi_eightyTwoCB_96945884496431434735931651260, phi_eightyTwoCB_96945884496431434735931651261, phi_eightyTwoCB_96945884496431434735931651262,
    phi_eightyTwoCB_96945884496431434735931651263, phi_eightyTwoCB_96945884496431434735931651264, phi_eightyTwoCB_96945884496431434735931651265,
    phi_eightyTwoCB_96945884496431434735931651266, phi_eightyTwoCB_96945884496431434735931651267, phi_eightyTwoCB_96945884496431434735931651268,
    phi_eightyTwoCB_96945884496431434735931651269, phi_eightyTwoCB_96945884496431434735931651270, phi_eightyTwoCB_96945884496431434735931651271,
    phi_eightyTwoCB_96945884496431434735931651272, phi_eightyTwoCB_96945884496431434735931651273, phi_eightyTwoCB_96945884496431434735931651274,
    phi_eightyTwoCB_96945884496431434735931651275, phi_eightyTwoCB_96945884496431434735931651276, phi_eightyTwoCB_96945884496431434735931651277,
    phi_eightyTwoCB_96945884496431434735931651278, phi_eightyTwoCB_96945884496431434735931651279, phi_eightyTwoCB_96945884496431434735931651280,
    phi_eightyTwoCB_96945884496431434735931651281, phi_eightyTwoCB_96945884496431434735931651282, phi_eightyTwoCB_96945884496431434735931651283,
    phi_eightyTwoCB_96945884496431434735931651284, phi_eightyTwoCB_96945884496431434735931651285, phi_eightyTwoCB_96945884496431434735931651286,
    phi_eightyTwoCB_96945884496431434735931651287, phi_eightyTwoCB_96945884496431434735931651288, phi_eightyTwoCB_96945884496431434735931651289,
    phi_eightyTwoCB_96945884496431434735931651290, phi_eightyTwoCB_96945884496431434735931651291, phi_eightyTwoCB_96945884496431434735931651292,
    phi_eightyTwoCB_96945884496431434735931651293, phi_eightyTwoCB_96945884496431434735931651294, phi_eightyTwoCB_96945884496431434735931651295,
    phi_eightyTwoCB_96945884496431434735931651296, phi_eightyTwoCB_96945884496431434735931651297, phi_eightyTwoCB_96945884496431434735931651298,
    phi_eightyTwoCB_96945884496431434735931651299, phi_eightyTwoCB_96945884496431434735931651300, phi_eightyTwoCB_96945884496431434735931651301]

end TotientTailPeriodKiller
end Erdos249257
