import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyThreeBSFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyThreeBSFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventyThreeBSFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyThreeBSFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyThreeBSFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyThreeBSFastPow a n * seventyThreeBSFastPow a n * a else seventyThreeBSFastPow a n * seventyThreeBSFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyThreeBS_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventyThreeBS_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventyThreeBS_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventyThreeBS_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventyThreeBS_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventyThreeBS_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventyThreeBS_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventyThreeBS_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventyThreeBS_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventyThreeBS_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventyThreeBS_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventyThreeBS_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventyThreeBS_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventyThreeBS_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventyThreeBS_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventyThreeBS_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventyThreeBS_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventyThreeBS_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventyThreeBS_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventyThreeBS_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventyThreeBS_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventyThreeBS_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventyThreeBS_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventyThreeBS_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventyThreeBS_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventyThreeBS_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventyThreeBS_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventyThreeBS_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventyThreeBS_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventyThreeBS_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventyThreeBS_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventyThreeBS_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventyThreeBS_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventyThreeBS_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventyThreeBS_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventyThreeBS_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventyThreeBS_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventyThreeBS_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventyThreeBS_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventyThreeBS_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventyThreeBS_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventyThreeBS_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventyThreeBS_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventyThreeBS_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventyThreeBS_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventyThreeBS_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventyThreeBS_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventyThreeBS_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventyThreeBS_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventyThreeBS_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventyThreeBS_257 : Nat.Prime 257 := by norm_num
private theorem prime_seventyThreeBS_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventyThreeBS_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventyThreeBS_271 : Nat.Prime 271 := by norm_num
private theorem prime_seventyThreeBS_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventyThreeBS_281 : Nat.Prime 281 := by norm_num
private theorem prime_seventyThreeBS_283 : Nat.Prime 283 := by norm_num
private theorem prime_seventyThreeBS_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventyThreeBS_311 : Nat.Prime 311 := by norm_num
private theorem prime_seventyThreeBS_313 : Nat.Prime 313 := by norm_num
private theorem prime_seventyThreeBS_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventyThreeBS_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventyThreeBS_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventyThreeBS_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventyThreeBS_373 : Nat.Prime 373 := by norm_num
private theorem prime_seventyThreeBS_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventyThreeBS_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventyThreeBS_397 : Nat.Prime 397 := by norm_num
private theorem prime_seventyThreeBS_401 : Nat.Prime 401 := by norm_num
private theorem prime_seventyThreeBS_419 : Nat.Prime 419 := by norm_num
private theorem prime_seventyThreeBS_431 : Nat.Prime 431 := by norm_num
private theorem prime_seventyThreeBS_433 : Nat.Prime 433 := by norm_num
private theorem prime_seventyThreeBS_439 : Nat.Prime 439 := by norm_num
private theorem prime_seventyThreeBS_443 : Nat.Prime 443 := by norm_num
private theorem prime_seventyThreeBS_449 : Nat.Prime 449 := by norm_num
private theorem prime_seventyThreeBS_463 : Nat.Prime 463 := by norm_num
private theorem prime_seventyThreeBS_479 : Nat.Prime 479 := by norm_num
private theorem prime_seventyThreeBS_499 : Nat.Prime 499 := by norm_num
private theorem prime_seventyThreeBS_509 : Nat.Prime 509 := by norm_num
private theorem prime_seventyThreeBS_523 : Nat.Prime 523 := by norm_num
private theorem prime_seventyThreeBS_547 : Nat.Prime 547 := by norm_num
private theorem prime_seventyThreeBS_557 : Nat.Prime 557 := by norm_num
private theorem prime_seventyThreeBS_571 : Nat.Prime 571 := by norm_num
private theorem prime_seventyThreeBS_607 : Nat.Prime 607 := by norm_num
private theorem prime_seventyThreeBS_643 : Nat.Prime 643 := by norm_num
private theorem prime_seventyThreeBS_647 : Nat.Prime 647 := by norm_num
private theorem prime_seventyThreeBS_661 : Nat.Prime 661 := by norm_num
private theorem prime_seventyThreeBS_701 : Nat.Prime 701 := by norm_num
private theorem prime_seventyThreeBS_727 : Nat.Prime 727 := by norm_num
private theorem prime_seventyThreeBS_743 : Nat.Prime 743 := by norm_num
private theorem prime_seventyThreeBS_757 : Nat.Prime 757 := by norm_num
private theorem prime_seventyThreeBS_809 : Nat.Prime 809 := by norm_num
private theorem prime_seventyThreeBS_823 : Nat.Prime 823 := by norm_num
private theorem prime_seventyThreeBS_839 : Nat.Prime 839 := by norm_num
private theorem prime_seventyThreeBS_859 : Nat.Prime 859 := by norm_num
private theorem prime_seventyThreeBS_863 : Nat.Prime 863 := by norm_num
private theorem prime_seventyThreeBS_881 : Nat.Prime 881 := by norm_num
private theorem prime_seventyThreeBS_911 : Nat.Prime 911 := by norm_num
private theorem prime_seventyThreeBS_947 : Nat.Prime 947 := by norm_num
private theorem prime_seventyThreeBS_977 : Nat.Prime 977 := by norm_num
private theorem prime_seventyThreeBS_997 : Nat.Prime 997 := by norm_num
private theorem prime_seventyThreeBS_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_seventyThreeBS_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_seventyThreeBS_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_seventyThreeBS_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_seventyThreeBS_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_seventyThreeBS_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_seventyThreeBS_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_seventyThreeBS_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_seventyThreeBS_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_seventyThreeBS_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_seventyThreeBS_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_seventyThreeBS_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_seventyThreeBS_1297 : Nat.Prime 1297 := by norm_num
private theorem prime_seventyThreeBS_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_seventyThreeBS_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_seventyThreeBS_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_seventyThreeBS_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_seventyThreeBS_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_seventyThreeBS_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_seventyThreeBS_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_seventyThreeBS_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_seventyThreeBS_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_seventyThreeBS_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_seventyThreeBS_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_seventyThreeBS_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_seventyThreeBS_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_seventyThreeBS_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_seventyThreeBS_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_seventyThreeBS_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_seventyThreeBS_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_seventyThreeBS_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_seventyThreeBS_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_seventyThreeBS_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_seventyThreeBS_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_seventyThreeBS_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_seventyThreeBS_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_seventyThreeBS_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_seventyThreeBS_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_seventyThreeBS_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_seventyThreeBS_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_seventyThreeBS_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_seventyThreeBS_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_seventyThreeBS_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_seventyThreeBS_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_seventyThreeBS_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_seventyThreeBS_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_seventyThreeBS_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_seventyThreeBS_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_seventyThreeBS_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_seventyThreeBS_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_seventyThreeBS_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_seventyThreeBS_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_seventyThreeBS_3037 : Nat.Prime 3037 := by norm_num
private theorem prime_seventyThreeBS_3083 : Nat.Prime 3083 := by norm_num
private theorem prime_seventyThreeBS_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_seventyThreeBS_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_seventyThreeBS_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_seventyThreeBS_3343 : Nat.Prime 3343 := by norm_num
private theorem prime_seventyThreeBS_3529 : Nat.Prime 3529 := by norm_num
private theorem prime_seventyThreeBS_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_seventyThreeBS_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_seventyThreeBS_3701 : Nat.Prime 3701 := by norm_num
private theorem prime_seventyThreeBS_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_seventyThreeBS_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_seventyThreeBS_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_seventyThreeBS_4337 : Nat.Prime 4337 := by norm_num
private theorem prime_seventyThreeBS_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_seventyThreeBS_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_seventyThreeBS_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_seventyThreeBS_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_seventyThreeBS_4723 : Nat.Prime 4723 := by norm_num
private theorem prime_seventyThreeBS_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_seventyThreeBS_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_seventyThreeBS_5081 : Nat.Prime 5081 := by norm_num
private theorem prime_seventyThreeBS_5281 : Nat.Prime 5281 := by norm_num
private theorem prime_seventyThreeBS_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_seventyThreeBS_5581 : Nat.Prime 5581 := by norm_num
private theorem prime_seventyThreeBS_5717 : Nat.Prime 5717 := by norm_num
private theorem prime_seventyThreeBS_5791 : Nat.Prime 5791 := by norm_num
private theorem prime_seventyThreeBS_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_seventyThreeBS_6263 : Nat.Prime 6263 := by norm_num
private theorem prime_seventyThreeBS_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_seventyThreeBS_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_seventyThreeBS_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_seventyThreeBS_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_seventyThreeBS_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_seventyThreeBS_6907 : Nat.Prime 6907 := by norm_num
private theorem prime_seventyThreeBS_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_seventyThreeBS_7297 : Nat.Prime 7297 := by norm_num
private theorem prime_seventyThreeBS_7639 : Nat.Prime 7639 := by norm_num
private theorem prime_seventyThreeBS_7717 : Nat.Prime 7717 := by norm_num
private theorem prime_seventyThreeBS_7933 : Nat.Prime 7933 := by norm_num
private theorem prime_seventyThreeBS_7963 : Nat.Prime 7963 := by norm_num
private theorem prime_seventyThreeBS_8081 : Nat.Prime 8081 := by norm_num
private theorem prime_seventyThreeBS_8231 : Nat.Prime 8231 := by norm_num
private theorem prime_seventyThreeBS_8753 : Nat.Prime 8753 := by norm_num
private theorem prime_seventyThreeBS_9127 : Nat.Prime 9127 := by norm_num
private theorem prime_seventyThreeBS_9227 : Nat.Prime 9227 := by norm_num
private theorem prime_seventyThreeBS_9337 : Nat.Prime 9337 := by norm_num
private theorem prime_seventyThreeBS_9413 : Nat.Prime 9413 := by norm_num
private theorem prime_seventyThreeBS_9547 : Nat.Prime 9547 := by norm_num
private theorem prime_seventyThreeBS_9883 : Nat.Prime 9883 := by norm_num
private theorem prime_seventyThreeBS_9973 : Nat.Prime 9973 := by norm_num
private theorem prime_seventyThreeBS_10663 : Nat.Prime 10663 := by norm_num
private theorem prime_seventyThreeBS_11579 : Nat.Prime 11579 := by norm_num
private theorem prime_seventyThreeBS_11981 : Nat.Prime 11981 := by norm_num
private theorem prime_seventyThreeBS_13003 : Nat.Prime 13003 := by norm_num
private theorem prime_seventyThreeBS_13591 : Nat.Prime 13591 := by norm_num
private theorem prime_seventyThreeBS_14221 : Nat.Prime 14221 := by norm_num
private theorem prime_seventyThreeBS_14797 : Nat.Prime 14797 := by norm_num
private theorem prime_seventyThreeBS_15667 : Nat.Prime 15667 := by norm_num
private theorem prime_seventyThreeBS_16603 : Nat.Prime 16603 := by norm_num
private theorem prime_seventyThreeBS_16937 : Nat.Prime 16937 := by norm_num
private theorem prime_seventyThreeBS_17483 : Nat.Prime 17483 := by norm_num
private theorem prime_seventyThreeBS_18181 : Nat.Prime 18181 := by norm_num
private theorem prime_seventyThreeBS_19759 : Nat.Prime 19759 := by norm_num
private theorem prime_seventyThreeBS_20327 : Nat.Prime 20327 := by norm_num
private theorem prime_seventyThreeBS_20479 : Nat.Prime 20479 := by norm_num
private theorem prime_seventyThreeBS_21179 : Nat.Prime 21179 := by norm_num
private theorem prime_seventyThreeBS_21419 : Nat.Prime 21419 := by norm_num
private theorem prime_seventyThreeBS_22013 : Nat.Prime 22013 := by norm_num
private theorem prime_seventyThreeBS_22453 : Nat.Prime 22453 := by norm_num
private theorem prime_seventyThreeBS_23297 : Nat.Prime 23297 := by norm_num
private theorem prime_seventyThreeBS_23677 : Nat.Prime 23677 := by norm_num
private theorem prime_seventyThreeBS_24677 : Nat.Prime 24677 := by norm_num
private theorem prime_seventyThreeBS_24923 : Nat.Prime 24923 := by norm_num
private theorem prime_seventyThreeBS_25087 : Nat.Prime 25087 := by norm_num
private theorem prime_seventyThreeBS_25583 : Nat.Prime 25583 := by norm_num
private theorem prime_seventyThreeBS_26161 : Nat.Prime 26161 := by norm_num
private theorem prime_seventyThreeBS_26927 : Nat.Prime 26927 := by norm_num
private theorem prime_seventyThreeBS_27431 : Nat.Prime 27431 := by norm_num
private theorem prime_seventyThreeBS_28387 : Nat.Prime 28387 := by norm_num
private theorem prime_seventyThreeBS_30763 : Nat.Prime 30763 := by norm_num
private theorem prime_seventyThreeBS_30841 : Nat.Prime 30841 := by norm_num
private theorem prime_seventyThreeBS_32479 : Nat.Prime 32479 := by norm_num
private theorem prime_seventyThreeBS_32537 : Nat.Prime 32537 := by norm_num
private theorem prime_seventyThreeBS_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_seventyThreeBS_33623 : Nat.Prime 33623 := by norm_num
private theorem prime_seventyThreeBS_35051 : Nat.Prime 35051 := by norm_num
private theorem prime_seventyThreeBS_36527 : Nat.Prime 36527 := by norm_num
private theorem prime_seventyThreeBS_36877 : Nat.Prime 36877 := by norm_num
private theorem prime_seventyThreeBS_38069 : Nat.Prime 38069 := by norm_num
private theorem prime_seventyThreeBS_38273 : Nat.Prime 38273 := by norm_num
private theorem prime_seventyThreeBS_38281 : Nat.Prime 38281 := by norm_num
private theorem prime_seventyThreeBS_39521 : Nat.Prime 39521 := by norm_num
private theorem prime_seventyThreeBS_39857 : Nat.Prime 39857 := by norm_num
private theorem prime_seventyThreeBS_41243 : Nat.Prime 41243 := by norm_num
private theorem prime_seventyThreeBS_41579 : Nat.Prime 41579 := by norm_num
private theorem prime_seventyThreeBS_42701 : Nat.Prime 42701 := by norm_num
private theorem prime_seventyThreeBS_42839 : Nat.Prime 42839 := by norm_num
private theorem prime_seventyThreeBS_44053 : Nat.Prime 44053 := by norm_num
private theorem prime_seventyThreeBS_48673 : Nat.Prime 48673 := by norm_num
private theorem prime_seventyThreeBS_50417 : Nat.Prime 50417 := by norm_num
private theorem prime_seventyThreeBS_54323 : Nat.Prime 54323 := by norm_num
private theorem prime_seventyThreeBS_55717 : Nat.Prime 55717 := by norm_num
private theorem prime_seventyThreeBS_56629 : Nat.Prime 56629 := by norm_num
private theorem prime_seventyThreeBS_59113 : Nat.Prime 59113 := by norm_num
private theorem prime_seventyThreeBS_61231 : Nat.Prime 61231 := by norm_num
private theorem prime_seventyThreeBS_67957 : Nat.Prime 67957 := by norm_num
private theorem prime_seventyThreeBS_74699 : Nat.Prime 74699 := by norm_num
private theorem prime_seventyThreeBS_77951 : Nat.Prime 77951 := by norm_num
private theorem prime_seventyThreeBS_78193 : Nat.Prime 78193 := by norm_num
private theorem prime_seventyThreeBS_80471 : Nat.Prime 80471 := by norm_num
private theorem prime_seventyThreeBS_90053 : Nat.Prime 90053 := by norm_num
private theorem prime_seventyThreeBS_99761 : Nat.Prime 99761 := by norm_num
private theorem prime_seventyThreeBS_103687 : Nat.Prime 103687 := by norm_num
private theorem prime_seventyThreeBS_106219 : Nat.Prime 106219 := by norm_num
private theorem prime_seventyThreeBS_106859 : Nat.Prime 106859 := by norm_num
private theorem prime_seventyThreeBS_112303 : Nat.Prime 112303 := by norm_num
private theorem prime_seventyThreeBS_115279 : Nat.Prime 115279 := by norm_num
private theorem prime_seventyThreeBS_117619 : Nat.Prime 117619 := by norm_num
private theorem prime_seventyThreeBS_121343 : Nat.Prime 121343 := by norm_num
private theorem prime_seventyThreeBS_125029 : Nat.Prime 125029 := by norm_num
private theorem prime_seventyThreeBS_126031 : Nat.Prime 126031 := by norm_num
private theorem prime_seventyThreeBS_127133 : Nat.Prime 127133 := by norm_num
private theorem prime_seventyThreeBS_135241 : Nat.Prime 135241 := by norm_num
private theorem prime_seventyThreeBS_139987 : Nat.Prime 139987 := by norm_num
private theorem prime_seventyThreeBS_145121 : Nat.Prime 145121 := by norm_num
private theorem prime_seventyThreeBS_147743 : Nat.Prime 147743 := by norm_num
private theorem prime_seventyThreeBS_150617 : Nat.Prime 150617 := by norm_num
private theorem prime_seventyThreeBS_160357 : Nat.Prime 160357 := by norm_num
private theorem prime_seventyThreeBS_163367 : Nat.Prime 163367 := by norm_num
private theorem prime_seventyThreeBS_163861 : Nat.Prime 163861 := by norm_num
private theorem prime_seventyThreeBS_176047 : Nat.Prime 176047 := by norm_num
private theorem prime_seventyThreeBS_178307 : Nat.Prime 178307 := by norm_num
private theorem prime_seventyThreeBS_181183 : Nat.Prime 181183 := by norm_num
private theorem prime_seventyThreeBS_187931 : Nat.Prime 187931 := by norm_num
private theorem prime_seventyThreeBS_201911 : Nat.Prime 201911 := by norm_num
private theorem prime_seventyThreeBS_208799 : Nat.Prime 208799 := by norm_num
private theorem prime_seventyThreeBS_217241 : Nat.Prime 217241 := by norm_num
private theorem prime_seventyThreeBS_218003 : Nat.Prime 218003 := by norm_num
private theorem prime_seventyThreeBS_219727 : Nat.Prime 219727 := by norm_num
private theorem prime_seventyThreeBS_229753 : Nat.Prime 229753 := by norm_num
private theorem prime_seventyThreeBS_237271 : Nat.Prime 237271 := by norm_num
private theorem prime_seventyThreeBS_241117 : Nat.Prime 241117 := by norm_num
private theorem prime_seventyThreeBS_241739 : Nat.Prime 241739 := by norm_num
private theorem prime_seventyThreeBS_244507 : Nat.Prime 244507 := by norm_num
private theorem prime_seventyThreeBS_255757 : Nat.Prime 255757 := by norm_num
private theorem prime_seventyThreeBS_255961 : Nat.Prime 255961 := by norm_num
private theorem prime_seventyThreeBS_305231 : Nat.Prime 305231 := by norm_num
private theorem prime_seventyThreeBS_323699 : Nat.Prime 323699 := by norm_num
private theorem prime_seventyThreeBS_326149 : Nat.Prime 326149 := by norm_num
private theorem prime_seventyThreeBS_331339 : Nat.Prime 331339 := by norm_num
private theorem prime_seventyThreeBS_332191 : Nat.Prime 332191 := by norm_num
private theorem prime_seventyThreeBS_340519 : Nat.Prime 340519 := by norm_num
private theorem prime_seventyThreeBS_365419 : Nat.Prime 365419 := by norm_num
private theorem prime_seventyThreeBS_371929 : Nat.Prime 371929 := by norm_num
private theorem prime_seventyThreeBS_398033 : Nat.Prime 398033 := by norm_num
private theorem prime_seventyThreeBS_405299 : Nat.Prime 405299 := by norm_num
private theorem prime_seventyThreeBS_406093 : Nat.Prime 406093 := by norm_num
private theorem prime_seventyThreeBS_444403 : Nat.Prime 444403 := by norm_num
private theorem prime_seventyThreeBS_471703 : Nat.Prime 471703 := by norm_num
private theorem prime_seventyThreeBS_490183 : Nat.Prime 490183 := by norm_num
private theorem prime_seventyThreeBS_542281 : Nat.Prime 542281 := by norm_num
private theorem prime_seventyThreeBS_558829 : Nat.Prime 558829 := by norm_num
private theorem prime_seventyThreeBS_564409 : Nat.Prime 564409 := by norm_num
private theorem prime_seventyThreeBS_569617 : Nat.Prime 569617 := by norm_num
private theorem prime_seventyThreeBS_635617 : Nat.Prime 635617 := by norm_num
private theorem prime_seventyThreeBS_636313 : Nat.Prime 636313 := by norm_num
private theorem prime_seventyThreeBS_647723 : Nat.Prime 647723 := by norm_num
private theorem prime_seventyThreeBS_659437 : Nat.Prime 659437 := by norm_num
private theorem prime_seventyThreeBS_691531 : Nat.Prime 691531 := by norm_num
private theorem prime_seventyThreeBS_711499 : Nat.Prime 711499 := by norm_num
private theorem prime_seventyThreeBS_751327 : Nat.Prime 751327 := by norm_num
private theorem prime_seventyThreeBS_782053 : Nat.Prime 782053 := by norm_num
private theorem prime_seventyThreeBS_792293 : Nat.Prime 792293 := by norm_num
private theorem prime_seventyThreeBS_876851 : Nat.Prime 876851 := by norm_num
private theorem prime_seventyThreeBS_951449 : Nat.Prime 951449 := by norm_num
private theorem prime_seventyThreeBS_954763 : Nat.Prime 954763 := by norm_num
private theorem prime_seventyThreeBS_1018789 : Nat.Prime 1018789 := by norm_num
private theorem prime_seventyThreeBS_1020989 : Nat.Prime 1020989 := by norm_num
private theorem prime_seventyThreeBS_1050253 : Nat.Prime 1050253 := by norm_num
private theorem prime_seventyThreeBS_1057853 : Nat.Prime 1057853 := by norm_num
private theorem prime_seventyThreeBS_1069609 : Nat.Prime 1069609 := by norm_num
private theorem prime_seventyThreeBS_1097323 : Nat.Prime 1097323 := by norm_num
private theorem prime_seventyThreeBS_1113187 : Nat.Prime 1113187 := by norm_num
private theorem prime_seventyThreeBS_1129477 : Nat.Prime 1129477 := by norm_num
private theorem prime_seventyThreeBS_1172539 : Nat.Prime 1172539 := by norm_num
private theorem prime_seventyThreeBS_1185013 : Nat.Prime 1185013 := by norm_num
private theorem prime_seventyThreeBS_1258973 : Nat.Prime 1258973 := by norm_num
private theorem prime_seventyThreeBS_1259543 : Nat.Prime 1259543 := by norm_num
private theorem prime_seventyThreeBS_1275539 : Nat.Prime 1275539 := by norm_num
private theorem prime_seventyThreeBS_1471307 : Nat.Prime 1471307 := by norm_num
private theorem prime_seventyThreeBS_1487389 : Nat.Prime 1487389 := by norm_num
private theorem prime_seventyThreeBS_1581317 : Nat.Prime 1581317 := by norm_num
private theorem prime_seventyThreeBS_1594063 : Nat.Prime 1594063 := by norm_num
private theorem prime_seventyThreeBS_1615403 : Nat.Prime 1615403 := by norm_num
private theorem prime_seventyThreeBS_1691527 : Nat.Prime 1691527 := by norm_num
private theorem prime_seventyThreeBS_1827107 : Nat.Prime 1827107 := by norm_num
private theorem prime_seventyThreeBS_1885349 : Nat.Prime 1885349 := by norm_num
private theorem prime_seventyThreeBS_1952653 : Nat.Prime 1952653 := by norm_num
private theorem prime_seventyThreeBS_1973627 : Nat.Prime 1973627 := by norm_num
private theorem prime_seventyThreeBS_2094203 : Nat.Prime 2094203 := by norm_num
private theorem prime_seventyThreeBS_2107873 : Nat.Prime 2107873 := by norm_num
private theorem prime_seventyThreeBS_2129527 : Nat.Prime 2129527 := by norm_num
private theorem prime_seventyThreeBS_2148203 : Nat.Prime 2148203 := by norm_num
private theorem prime_seventyThreeBS_2377621 : Nat.Prime 2377621 := by norm_num
private theorem prime_seventyThreeBS_2444119 : Nat.Prime 2444119 := by norm_num
private theorem prime_seventyThreeBS_2470957 : Nat.Prime 2470957 := by norm_num
private theorem prime_seventyThreeBS_2807561 : Nat.Prime 2807561 := by norm_num
private theorem prime_seventyThreeBS_2925641 : Nat.Prime 2925641 := by norm_num
private theorem prime_seventyThreeBS_2949013 : Nat.Prime 2949013 := by norm_num
private theorem prime_seventyThreeBS_2965961 : Nat.Prime 2965961 := by norm_num
private theorem prime_seventyThreeBS_2984803 : Nat.Prime 2984803 := by norm_num
private theorem prime_seventyThreeBS_2993371 : Nat.Prime 2993371 := by norm_num
private theorem prime_seventyThreeBS_3005237 : Nat.Prime 3005237 := by norm_num
private theorem prime_seventyThreeBS_3114317 : Nat.Prime 3114317 := by norm_num
private theorem prime_seventyThreeBS_3142487 : Nat.Prime 3142487 := by norm_num
private theorem prime_seventyThreeBS_3149749 : Nat.Prime 3149749 := by norm_num
private theorem prime_seventyThreeBS_3382781 : Nat.Prime 3382781 := by norm_num
private theorem prime_seventyThreeBS_3422437 : Nat.Prime 3422437 := by norm_num
private theorem prime_seventyThreeBS_3786859 : Nat.Prime 3786859 := by norm_num
private theorem prime_seventyThreeBS_3792637 : Nat.Prime 3792637 := by norm_num
private theorem prime_seventyThreeBS_3913993 : Nat.Prime 3913993 := by norm_num
private theorem prime_seventyThreeBS_4208641 : Nat.Prime 4208641 := by norm_num
private theorem prime_seventyThreeBS_4612819 : Nat.Prime 4612819 := by norm_num
private theorem prime_seventyThreeBS_4765249 : Nat.Prime 4765249 := by norm_num
private theorem prime_seventyThreeBS_4777057 : Nat.Prime 4777057 := by norm_num
private theorem prime_seventyThreeBS_4908961 : Nat.Prime 4908961 := by norm_num
private theorem prime_seventyThreeBS_4976171 : Nat.Prime 4976171 := by norm_num
private theorem prime_seventyThreeBS_5298299 : Nat.Prime 5298299 := by norm_num
private theorem prime_seventyThreeBS_5475121 : Nat.Prime 5475121 := by norm_num
private theorem prime_seventyThreeBS_5983597 : Nat.Prime 5983597 := by norm_num
private theorem prime_seventyThreeBS_6217993 : Nat.Prime 6217993 := by norm_num
private theorem prime_seventyThreeBS_6225889 : Nat.Prime 6225889 := by norm_num
private theorem prime_seventyThreeBS_6427951 : Nat.Prime 6427951 := by norm_num
private theorem prime_seventyThreeBS_6535541 : Nat.Prime 6535541 := by norm_num
private theorem prime_seventyThreeBS_6569011 : Nat.Prime 6569011 := by norm_num
private theorem prime_seventyThreeBS_6674483 : Nat.Prime 6674483 := by norm_num
private theorem prime_seventyThreeBS_7009643 : Nat.Prime 7009643 := by norm_num
private theorem prime_seventyThreeBS_7212253 : Nat.Prime 7212253 := by norm_num
private theorem prime_seventyThreeBS_7226363 : Nat.Prime 7226363 := by norm_num
private theorem prime_seventyThreeBS_7366349 : Nat.Prime 7366349 := by norm_num
private theorem prime_seventyThreeBS_7507889 : Nat.Prime 7507889 := by norm_num
private theorem prime_seventyThreeBS_7940467 : Nat.Prime 7940467 := by norm_num
private theorem prime_seventyThreeBS_7995341 : Nat.Prime 7995341 := by norm_num
private theorem prime_seventyThreeBS_8474821 : Nat.Prime 8474821 := by norm_num
private theorem prime_seventyThreeBS_9702041 : Nat.Prime 9702041 := by norm_num
private theorem prime_seventyThreeBS_10098953 : Nat.Prime 10098953 := by norm_num
private theorem prime_seventyThreeBS_10164127 : Nat.Prime 10164127 := by norm_num
private theorem prime_seventyThreeBS_10956527 : Nat.Prime 10956527 := by norm_num
private theorem prime_seventyThreeBS_11552011 : Nat.Prime 11552011 := by norm_num
private theorem prime_seventyThreeBS_12489721 : Nat.Prime 12489721 := by norm_num
private theorem prime_seventyThreeBS_13559701 : Nat.Prime 13559701 := by norm_num
private theorem prime_seventyThreeBS_14169941 : Nat.Prime 14169941 := by norm_num
private theorem prime_seventyThreeBS_14265893 : Nat.Prime 14265893 := by norm_num
private theorem prime_seventyThreeBS_14544223 : Nat.Prime 14544223 := by norm_num
private theorem prime_seventyThreeBS_14644039 : Nat.Prime 14644039 := by norm_num
private theorem prime_seventyThreeBS_15442033 : Nat.Prime 15442033 := by norm_num
private theorem prime_seventyThreeBS_16044059 : Nat.Prime 16044059 := by norm_num
private theorem prime_seventyThreeBS_16670317 : Nat.Prime 16670317 := by norm_num
private theorem prime_seventyThreeBS_16729369 : Nat.Prime 16729369 := by norm_num
private theorem prime_seventyThreeBS_17180399 : Nat.Prime 17180399 := by norm_num
private theorem prime_seventyThreeBS_19415699 : Nat.Prime 19415699 := by norm_num
private theorem prime_seventyThreeBS_20338363 : Nat.Prime 20338363 := by norm_num
private theorem prime_seventyThreeBS_20661913 : Nat.Prime 20661913 := by norm_num
private theorem prime_seventyThreeBS_21083911 : Nat.Prime 21083911 := by norm_num
private theorem prime_seventyThreeBS_21480541 : Nat.Prime 21480541 := by norm_num
private theorem prime_seventyThreeBS_22673473 : Nat.Prime 22673473 := by norm_num
private theorem prime_seventyThreeBS_23161363 : Nat.Prime 23161363 := by norm_num
private theorem prime_seventyThreeBS_23739061 : Nat.Prime 23739061 := by norm_num
private theorem prime_seventyThreeBS_24022367 : Nat.Prime 24022367 := by norm_num
private theorem prime_seventyThreeBS_24383839 : Nat.Prime 24383839 := by norm_num
private theorem prime_seventyThreeBS_26633279 : Nat.Prime 26633279 := by norm_num
private theorem prime_seventyThreeBS_26945647 : Nat.Prime 26945647 := by norm_num
private theorem prime_seventyThreeBS_28149211 : Nat.Prime 28149211 := by norm_num
private theorem prime_seventyThreeBS_28433239 : Nat.Prime 28433239 := by norm_num
private theorem prime_seventyThreeBS_29874521 : Nat.Prime 29874521 := by norm_num
private theorem prime_seventyThreeBS_36063697 : Nat.Prime 36063697 := by
  apply lucas_primality 36063697 (5 : ZMod 36063697)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (751327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (751327, 1)] : List FactorBlock).map factorBlockValue).prod) = 36063697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_751327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 36063697) ^ 18031848 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 36063697) ^ 12021232 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 36063697) ^ 48 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_36563479 : Nat.Prime 36563479 := by
  apply lucas_primality 36563479 (3 : ZMod 36563479)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (383, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (383, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 36563479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_383
      · exact prime_seventyThreeBS_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36563479) ^ 18281739 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 36563479) ^ 12187826 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 36563479) ^ 5223354 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 36563479) ^ 95466 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 36563479) ^ 16086 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_37115443 : Nat.Prime 37115443 := by
  apply lucas_primality 37115443 (2 : ZMod 37115443)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (13, 2), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (13, 2), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 37115443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37115443) ^ 18557721 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37115443) ^ 12371814 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37115443) ^ 5302206 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37115443) ^ 2855034 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37115443) ^ 447174 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_44248417 : Nat.Prime 44248417 := by
  apply lucas_primality 44248417 (13 : ZMod 44248417)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (19, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (19, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) = 44248417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_1427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 44248417) ^ 22124208 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 44248417) ^ 14749472 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 44248417) ^ 2602848 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 44248417) ^ 2328864 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 44248417) ^ 31008 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_48310541 : Nat.Prime 48310541 := by
  apply lucas_primality 48310541 (2 : ZMod 48310541)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (127133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (127133, 1)] : List FactorBlock).map factorBlockValue).prod) = 48310541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_127133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48310541) ^ 24155270 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48310541) ^ 9662108 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48310541) ^ 2542660 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48310541) ^ 380 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_55353829 : Nat.Prime 55353829 := by
  apply lucas_primality 55353829 (2 : ZMod 55353829)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4612819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4612819, 1)] : List FactorBlock).map factorBlockValue).prod) = 55353829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_4612819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55353829) ^ 27676914 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 55353829) ^ 18451276 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 55353829) ^ 12 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_56705543 : Nat.Prime 56705543 := by
  apply lucas_primality 56705543 (5 : ZMod 56705543)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (691531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (691531, 1)] : List FactorBlock).map factorBlockValue).prod) = 56705543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_691531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 56705543) ^ 28352771 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 56705543) ^ 1383062 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 56705543) ^ 82 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_57916171 : Nat.Prime 57916171 := by
  apply lucas_primality 57916171 (2 : ZMod 57916171)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (59, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (59, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 57916171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57916171) ^ 28958085 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916171) ^ 19305390 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916171) ^ 11583234 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916171) ^ 4455090 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916171) ^ 981630 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916171) ^ 69030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_68163463 : Nat.Prime 68163463 := by
  apply lucas_primality 68163463 (11 : ZMod 68163463)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3786859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3786859, 1)] : List FactorBlock).map factorBlockValue).prod) = 68163463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_3786859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 68163463) ^ 34081731 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 68163463) ^ 22721154 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 68163463) ^ 18 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_69347273 : Nat.Prime 69347273 := by
  apply lucas_primality 69347273 (3 : ZMod 69347273)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2437, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2437, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) = 69347273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_2437
      · exact prime_seventyThreeBS_3557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 69347273) ^ 34673636 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 69347273) ^ 28456 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 69347273) ^ 19496 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_70295509 : Nat.Prime 70295509 := by
  apply lucas_primality 70295509 (2 : ZMod 70295509)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1952653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1952653, 1)] : List FactorBlock).map factorBlockValue).prod) = 70295509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1952653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70295509) ^ 35147754 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70295509) ^ 23431836 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70295509) ^ 36 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_75297751 : Nat.Prime 75297751 := by
  apply lucas_primality 75297751 (3 : ZMod 75297751)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (11, 1), (9127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (11, 1), (9127, 1)] : List FactorBlock).map factorBlockValue).prod) = 75297751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_9127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75297751) ^ 37648875 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75297751) ^ 25099250 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75297751) ^ 15059550 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75297751) ^ 6845250 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 75297751) ^ 8250 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_78056327 : Nat.Prime 78056327 := by
  apply lucas_primality 78056327 (5 : ZMod 78056327)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1258973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1258973, 1)] : List FactorBlock).map factorBlockValue).prod) = 78056327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_1258973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 78056327) ^ 39028163 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 78056327) ^ 2517946 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 78056327) ^ 62 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_108081041 : Nat.Prime 108081041 := by
  apply lucas_primality 108081041 (3 : ZMod 108081041)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (911, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (911, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 108081041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_911
      · exact prime_seventyThreeBS_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 108081041) ^ 54040520 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 108081041) ^ 21616208 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 108081041) ^ 118640 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 108081041) ^ 72880 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_119734841 : Nat.Prime 119734841 := by
  apply lucas_primality 119734841 (3 : ZMod 119734841)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2993371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2993371, 1)] : List FactorBlock).map factorBlockValue).prod) = 119734841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_2993371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 119734841) ^ 59867420 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 119734841) ^ 23946968 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 119734841) ^ 40 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_121798099 : Nat.Prime 121798099 := by
  apply lucas_primality 121798099 (2 : ZMod 121798099)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (398033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (398033, 1)] : List FactorBlock).map factorBlockValue).prod) = 121798099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_398033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121798099) ^ 60899049 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 121798099) ^ 40599366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 121798099) ^ 7164594 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 121798099) ^ 306 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_133075763 : Nat.Prime 133075763 := by
  apply lucas_primality 133075763 (2 : ZMod 133075763)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3913993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3913993, 1)] : List FactorBlock).map factorBlockValue).prod) = 133075763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_3913993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 133075763) ^ 66537881 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133075763) ^ 7827986 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133075763) ^ 34 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_133583341 : Nat.Prime 133583341 := by
  apply lucas_primality 133583341 (2 : ZMod 133583341)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (31, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (31, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) = 133583341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_6529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133583341) ^ 66791670 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133583341) ^ 44527780 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133583341) ^ 26716668 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133583341) ^ 12143940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133583341) ^ 4309140 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 133583341) ^ 20460 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_137551489 : Nat.Prime 137551489 := by
  apply lucas_primality 137551489 (7 : ZMod 137551489)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (17, 1), (19, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (17, 1), (19, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 137551489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 137551489) ^ 68775744 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 137551489) ^ 45850496 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 137551489) ^ 8091264 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 137551489) ^ 7239552 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 137551489) ^ 124032 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_145617179 : Nat.Prime 145617179 := by
  apply lucas_primality 145617179 (2 : ZMod 145617179)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (29, 1), (43, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (29, 1), (43, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 145617179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_43
      · exact prime_seventyThreeBS_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145617179) ^ 72808589 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 145617179) ^ 20802454 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 145617179) ^ 7664062 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 145617179) ^ 5021282 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 145617179) ^ 3386446 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 145617179) ^ 331702 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_153433327 : Nat.Prime 153433327 := by
  apply lucas_primality 153433327 (3 : ZMod 153433327)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (323699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (323699, 1)] : List FactorBlock).map factorBlockValue).prod) = 153433327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_79
      · exact prime_seventyThreeBS_323699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 153433327) ^ 76716663 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 153433327) ^ 51144442 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 153433327) ^ 1942194 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 153433327) ^ 474 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_159447971 : Nat.Prime 159447971 := by
  apply lucas_primality 159447971 (6 : ZMod 159447971)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (47, 1), (30841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (47, 1), (30841, 1)] : List FactorBlock).map factorBlockValue).prod) = 159447971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_30841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 159447971) ^ 79723985 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 159447971) ^ 31889594 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 159447971) ^ 14495270 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 159447971) ^ 3392510 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 159447971) ^ 5170 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_173318491 : Nat.Prime 173318491 := by
  apply lucas_primality 173318491 (3 : ZMod 173318491)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (449, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (449, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 173318491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_449
      · exact prime_seventyThreeBS_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 173318491) ^ 86659245 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 173318491) ^ 57772830 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 173318491) ^ 34663698 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 173318491) ^ 386010 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 173318491) ^ 40410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_173330363 : Nat.Prime 173330363 := by
  apply lucas_primality 173330363 (2 : ZMod 173330363)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (127, 1), (22013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (127, 1), (22013, 1)] : List FactorBlock).map factorBlockValue).prod) = 173330363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_127
      · exact prime_seventyThreeBS_22013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 173330363) ^ 86665181 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173330363) ^ 5591302 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173330363) ^ 1364806 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 173330363) ^ 7874 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_189468193 : Nat.Prime 189468193 := by
  apply lucas_primality 189468193 (5 : ZMod 189468193)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1973627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1973627, 1)] : List FactorBlock).map factorBlockValue).prod) = 189468193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1973627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 189468193) ^ 94734096 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 189468193) ^ 63156064 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 189468193) ^ 96 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_191541871 : Nat.Prime 191541871 := by
  apply lucas_primality 191541871 (29 : ZMod 191541871)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (31, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (31, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) = 191541871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_5281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 191541871) ^ 95770935 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (29 : ZMod 191541871) ^ 63847290 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (29 : ZMod 191541871) ^ 38308374 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (29 : ZMod 191541871) ^ 14733990 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (29 : ZMod 191541871) ^ 6178770 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (29 : ZMod 191541871) ^ 36270 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_192246521 : Nat.Prime 192246521 := by
  apply lucas_primality 192246521 (6 : ZMod 192246521)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1187, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1187, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 192246521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_1187
      · exact prime_seventyThreeBS_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 192246521) ^ 96123260 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 192246521) ^ 38449304 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 192246521) ^ 161960 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 192246521) ^ 47480 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_196512227 : Nat.Prime 196512227 := by
  apply lucas_primality 196512227 (2 : ZMod 196512227)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (659437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (659437, 1)] : List FactorBlock).map factorBlockValue).prod) = 196512227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_149
      · exact prime_seventyThreeBS_659437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 196512227) ^ 98256113 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 196512227) ^ 1318874 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 196512227) ^ 298 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_216790891 : Nat.Prime 216790891 := by
  apply lucas_primality 216790891 (2 : ZMod 216790891)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7226363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7226363, 1)] : List FactorBlock).map factorBlockValue).prod) = 216790891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7226363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 216790891) ^ 108395445 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216790891) ^ 72263630 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216790891) ^ 43358178 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216790891) ^ 30 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_229211791 : Nat.Prime 229211791 := by
  apply lucas_primality 229211791 (3 : ZMod 229211791)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (332191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (332191, 1)] : List FactorBlock).map factorBlockValue).prod) = 229211791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_332191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 229211791) ^ 114605895 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 229211791) ^ 76403930 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 229211791) ^ 45842358 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 229211791) ^ 9965730 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 229211791) ^ 690 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_244060357 : Nat.Prime 244060357 := by
  apply lucas_primality 244060357 (5 : ZMod 244060357)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20338363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20338363, 1)] : List FactorBlock).map factorBlockValue).prod) = 244060357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_20338363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 244060357) ^ 122030178 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 244060357) ^ 81353452 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 244060357) ^ 12 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_255072647 : Nat.Prime 255072647 := by
  apply lucas_primality 255072647 (5 : ZMod 255072647)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (2965961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (2965961, 1)] : List FactorBlock).map factorBlockValue).prod) = 255072647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_43
      · exact prime_seventyThreeBS_2965961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 255072647) ^ 127536323 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 255072647) ^ 5931922 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 255072647) ^ 86 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_257784361 : Nat.Prime 257784361 := by
  apply lucas_primality 257784361 (11 : ZMod 257784361)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (2148203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (2148203, 1)] : List FactorBlock).map factorBlockValue).prod) = 257784361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_2148203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 257784361) ^ 128892180 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 257784361) ^ 85928120 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 257784361) ^ 51556872 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 257784361) ^ 120 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_260485759 : Nat.Prime 260485759 := by
  apply lucas_primality 260485759 (7 : ZMod 260485759)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1113187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1113187, 1)] : List FactorBlock).map factorBlockValue).prod) = 260485759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_1113187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 260485759) ^ 130242879 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 260485759) ^ 86828586 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 260485759) ^ 20037366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 260485759) ^ 234 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_264225743 : Nat.Prime 264225743 := by
  apply lucas_primality 264225743 (10 : ZMod 264225743)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (647, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (647, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 264225743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_647
      · exact prime_seventyThreeBS_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 264225743) ^ 132112871 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 264225743) ^ 24020522 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 264225743) ^ 13906618 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 264225743) ^ 408386 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 264225743) ^ 270446 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_266151527 : Nat.Prime 266151527 := by
  apply lucas_primality 266151527 (5 : ZMod 266151527)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (133075763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (133075763, 1)] : List FactorBlock).map factorBlockValue).prod) = 266151527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_133075763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 266151527) ^ 133075763 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 266151527) ^ 2 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_271283063 : Nat.Prime 271283063 := by
  apply lucas_primality 271283063 (5 : ZMod 271283063)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (757, 1), (3037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (757, 1), (3037, 1)] : List FactorBlock).map factorBlockValue).prod) = 271283063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_757
      · exact prime_seventyThreeBS_3037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 271283063) ^ 135641531 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 271283063) ^ 4598018 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 271283063) ^ 358366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 271283063) ^ 89326 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_279225581 : Nat.Prime 279225581 := by
  apply lucas_primality 279225581 (2 : ZMod 279225581)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (340519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (340519, 1)] : List FactorBlock).map factorBlockValue).prod) = 279225581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_340519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 279225581) ^ 139612790 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 279225581) ^ 55845116 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 279225581) ^ 6810380 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 279225581) ^ 820 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_291061231 : Nat.Prime 291061231 := by
  apply lucas_primality 291061231 (3 : ZMod 291061231)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9702041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9702041, 1)] : List FactorBlock).map factorBlockValue).prod) = 291061231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_9702041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 291061231) ^ 145530615 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 291061231) ^ 97020410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 291061231) ^ 58212246 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 291061231) ^ 30 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_295276393 : Nat.Prime 295276393 := by
  apply lucas_primality 295276393 (5 : ZMod 295276393)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (178307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (178307, 1)] : List FactorBlock).map factorBlockValue).prod) = 295276393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_178307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 295276393) ^ 147638196 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 295276393) ^ 98425464 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 295276393) ^ 12838104 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 295276393) ^ 1656 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_296586581 : Nat.Prime 296586581 := by
  apply lucas_primality 296586581 (2 : ZMod 296586581)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (113, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (113, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) = 296586581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_113
      · exact prime_seventyThreeBS_6907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 296586581) ^ 148293290 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 296586581) ^ 59317316 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 296586581) ^ 15609820 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 296586581) ^ 2624660 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 296586581) ^ 42940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_327064883 : Nat.Prime 327064883 := by
  apply lucas_primality 327064883 (2 : ZMod 327064883)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (636313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (636313, 1)] : List FactorBlock).map factorBlockValue).prod) = 327064883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_257
      · exact prime_seventyThreeBS_636313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 327064883) ^ 163532441 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327064883) ^ 1272626 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327064883) ^ 514 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_352771889 : Nat.Prime 352771889 := by
  apply lucas_primality 352771889 (3 : ZMod 352771889)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (3149749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (3149749, 1)] : List FactorBlock).map factorBlockValue).prod) = 352771889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_3149749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 352771889) ^ 176385944 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 352771889) ^ 50395984 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 352771889) ^ 112 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_378659863 : Nat.Prime 378659863 := by
  apply lucas_primality 378659863 (6 : ZMod 378659863)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3005237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3005237, 1)] : List FactorBlock).map factorBlockValue).prod) = 378659863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_3005237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 378659863) ^ 189329931 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 378659863) ^ 126219954 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 378659863) ^ 54094266 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 378659863) ^ 126 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_378793489 : Nat.Prime 378793489 := by
  apply lucas_primality 378793489 (11 : ZMod 378793489)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1433, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1433, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 378793489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1433
      · exact prime_seventyThreeBS_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 378793489) ^ 189396744 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 378793489) ^ 126264496 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 378793489) ^ 264336 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 378793489) ^ 68784 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_421947139 : Nat.Prime 421947139 := by
  apply lucas_primality 421947139 (2 : ZMod 421947139)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (241, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (241, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) = 421947139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_241
      · exact prime_seventyThreeBS_9413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421947139) ^ 210973569 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 421947139) ^ 140649046 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 421947139) ^ 13611198 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 421947139) ^ 1750818 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 421947139) ^ 44826 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_444417959 : Nat.Prime 444417959 := by
  apply lucas_primality 444417959 (13 : ZMod 444417959)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (463, 1), (3779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (463, 1), (3779, 1)] : List FactorBlock).map factorBlockValue).prod) = 444417959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_127
      · exact prime_seventyThreeBS_463
      · exact prime_seventyThreeBS_3779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 444417959) ^ 222208979 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 444417959) ^ 3499354 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 444417959) ^ 959866 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 444417959) ^ 117602 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_470818241 : Nat.Prime 470818241 := by
  apply lucas_primality 470818241 (3 : ZMod 470818241)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (1471307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (1471307, 1)] : List FactorBlock).map factorBlockValue).prod) = 470818241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_1471307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 470818241) ^ 235409120 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 470818241) ^ 94163648 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 470818241) ^ 320 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_509883287 : Nat.Prime 509883287 := by
  apply lucas_primality 509883287 (5 : ZMod 509883287)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (191, 1), (121343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (191, 1), (121343, 1)] : List FactorBlock).map factorBlockValue).prod) = 509883287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_191
      · exact prime_seventyThreeBS_121343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 509883287) ^ 254941643 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 509883287) ^ 46353026 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 509883287) ^ 2669546 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 509883287) ^ 4202 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_549652391 : Nat.Prime 549652391 := by
  apply lucas_primality 549652391 (7 : ZMod 549652391)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (37, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (37, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) = 549652391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_37
      · exact prime_seventyThreeBS_9227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 549652391) ^ 274826195 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 549652391) ^ 109930478 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 549652391) ^ 78521770 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 549652391) ^ 23897930 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 549652391) ^ 14855470 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 549652391) ^ 59570 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_555540613 : Nat.Prime 555540613 := by
  apply lucas_primality 555540613 (2 : ZMod 555540613)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (4208641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (4208641, 1)] : List FactorBlock).map factorBlockValue).prod) = 555540613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_4208641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 555540613) ^ 277770306 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 555540613) ^ 185180204 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 555540613) ^ 50503692 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 555540613) ^ 132 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_555832691 : Nat.Prime 555832691 := by
  apply lucas_primality 555832691 (6 : ZMod 555832691)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (7940467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (7940467, 1)] : List FactorBlock).map factorBlockValue).prod) = 555832691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_7940467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 555832691) ^ 277916345 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 555832691) ^ 111166538 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 555832691) ^ 79404670 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 555832691) ^ 70 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_686195857 : Nat.Prime 686195857 := by
  apply lucas_primality 686195857 (5 : ZMod 686195857)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (4765249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (4765249, 1)] : List FactorBlock).map factorBlockValue).prod) = 686195857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_4765249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 686195857) ^ 343097928 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 686195857) ^ 228731952 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 686195857) ^ 144 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_705244283 : Nat.Prime 705244283 := by
  apply lucas_primality 705244283 (2 : ZMod 705244283)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2003, 1), (176047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2003, 1), (176047, 1)] : List FactorBlock).map factorBlockValue).prod) = 705244283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_2003
      · exact prime_seventyThreeBS_176047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 705244283) ^ 352622141 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 705244283) ^ 352094 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 705244283) ^ 4006 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_720866051 : Nat.Prime 720866051 := by
  apply lucas_primality 720866051 (2 : ZMod 720866051)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (109, 1), (4561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (109, 1), (4561, 1)] : List FactorBlock).map factorBlockValue).prod) = 720866051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_109
      · exact prime_seventyThreeBS_4561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720866051) ^ 360433025 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 720866051) ^ 144173210 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 720866051) ^ 24857450 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 720866051) ^ 6613450 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 720866051) ^ 158050 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_761395003 : Nat.Prime 761395003 := by
  apply lucas_primality 761395003 (2 : ZMod 761395003)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9337, 1), (13591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9337, 1), (13591, 1)] : List FactorBlock).map factorBlockValue).prod) = 761395003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_9337
      · exact prime_seventyThreeBS_13591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 761395003) ^ 380697501 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 761395003) ^ 253798334 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 761395003) ^ 81546 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 761395003) ^ 56022 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_844476331 : Nat.Prime 844476331 := by
  apply lucas_primality 844476331 (2 : ZMod 844476331)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (28149211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (28149211, 1)] : List FactorBlock).map factorBlockValue).prod) = 844476331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_28149211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 844476331) ^ 422238165 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 844476331) ^ 281492110 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 844476331) ^ 168895266 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 844476331) ^ 30 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_864648329 : Nat.Prime 864648329 := by
  apply lucas_primality 864648329 (3 : ZMod 864648329)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (108081041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (108081041, 1)] : List FactorBlock).map factorBlockValue).prod) = 864648329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_108081041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 864648329) ^ 432324164 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 864648329) ^ 8 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_901056859 : Nat.Prime 901056859 := by
  apply lucas_primality 901056859 (2 : ZMod 901056859)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (11552011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (11552011, 1)] : List FactorBlock).map factorBlockValue).prod) = 901056859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_11552011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 901056859) ^ 450528429 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 901056859) ^ 300352286 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 901056859) ^ 69312066 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 901056859) ^ 78 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_926566397 : Nat.Prime 926566397 := by
  apply lucas_primality 926566397 (5 : ZMod 926566397)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (443, 1), (74699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (443, 1), (74699, 1)] : List FactorBlock).map factorBlockValue).prod) = 926566397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_443
      · exact prime_seventyThreeBS_74699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 926566397) ^ 463283198 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 926566397) ^ 132366628 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 926566397) ^ 2091572 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 926566397) ^ 12404 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1235489249 : Nat.Prime 1235489249 := by
  apply lucas_primality 1235489249 (3 : ZMod 1235489249)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (151, 1), (36527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (151, 1), (36527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235489249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_151
      · exact prime_seventyThreeBS_36527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1235489249) ^ 617744624 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235489249) ^ 176498464 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235489249) ^ 8182048 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235489249) ^ 33824 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1301881901 : Nat.Prime 1301881901 := by
  apply lucas_primality 1301881901 (2 : ZMod 1301881901)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (19, 1), (167, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (19, 1), (167, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1301881901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_167
      · exact prime_seventyThreeBS_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1301881901) ^ 650940950 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301881901) ^ 260376380 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301881901) ^ 118352900 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301881901) ^ 68520100 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301881901) ^ 7795700 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301881901) ^ 3490300 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1344855647 : Nat.Prime 1344855647 := by
  apply lucas_primality 1344855647 (5 : ZMod 1344855647)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5717, 1), (117619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5717, 1), (117619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1344855647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5717
      · exact prime_seventyThreeBS_117619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1344855647) ^ 672427823 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1344855647) ^ 235238 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1344855647) ^ 11434 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1375270747 : Nat.Prime 1375270747 := by
  apply lucas_primality 1375270747 (2 : ZMod 1375270747)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229211791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229211791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1375270747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_229211791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1375270747) ^ 687635373 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1375270747) ^ 458423582 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1375270747) ^ 6 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1479716377 : Nat.Prime 1479716377 := by
  apply lucas_primality 1479716377 (5 : ZMod 1479716377)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (97, 1), (635617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (97, 1), (635617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1479716377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_97
      · exact prime_seventyThreeBS_635617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1479716377) ^ 739858188 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1479716377) ^ 493238792 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1479716377) ^ 15254808 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1479716377) ^ 2328 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1546706167 : Nat.Prime 1546706167 := by
  apply lucas_primality 1546706167 (3 : ZMod 1546706167)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257784361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257784361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546706167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_257784361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1546706167) ^ 773353083 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1546706167) ^ 515568722 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1546706167) ^ 6 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1779222311 : Nat.Prime 1779222311 := by
  apply lucas_primality 1779222311 (11 : ZMod 1779222311)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8753, 1), (20327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8753, 1), (20327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1779222311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_8753
      · exact prime_seventyThreeBS_20327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1779222311) ^ 889611155 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1779222311) ^ 355844462 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1779222311) ^ 203270 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1779222311) ^ 87530 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1955451859 : Nat.Prime 1955451859 := by
  apply lucas_primality 1955451859 (2 : ZMod 1955451859)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (14169941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (14169941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1955451859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_14169941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1955451859) ^ 977725929 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955451859) ^ 651817286 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955451859) ^ 85019646 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955451859) ^ 138 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2074441757 : Nat.Prime 2074441757 := by
  apply lucas_primality 2074441757 (2 : ZMod 2074441757)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (16729369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (16729369, 1)] : List FactorBlock).map factorBlockValue).prod) = 2074441757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_16729369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2074441757) ^ 1037220878 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2074441757) ^ 66917476 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2074441757) ^ 124 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2112344441 : Nat.Prime 2112344441 := by
  apply lucas_primality 2112344441 (3 : ZMod 2112344441)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (281, 1), (187931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (281, 1), (187931, 1)] : List FactorBlock).map factorBlockValue).prod) = 2112344441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_281
      · exact prime_seventyThreeBS_187931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2112344441) ^ 1056172220 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2112344441) ^ 422468888 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2112344441) ^ 7517240 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2112344441) ^ 11240 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2506881961 : Nat.Prime 2506881961 := by
  apply lucas_primality 2506881961 (7 : ZMod 2506881961)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (11, 1), (31, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (11, 1), (31, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2506881961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2506881961) ^ 1253440980 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2506881961) ^ 835627320 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2506881961) ^ 501376392 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2506881961) ^ 227898360 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2506881961) ^ 80867160 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2506881961) ^ 1104840 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2686434577 : Nat.Prime 2686434577 := by
  apply lucas_primality 2686434577 (5 : ZMod 2686434577)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (7995341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (7995341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686434577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_7995341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2686434577) ^ 1343217288 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686434577) ^ 895478192 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686434577) ^ 383776368 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686434577) ^ 336 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2856524761 : Nat.Prime 2856524761 := by
  apply lucas_primality 2856524761 (7 : ZMod 2856524761)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (31, 1), (255961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (31, 1), (255961, 1)] : List FactorBlock).map factorBlockValue).prod) = 2856524761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_255961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2856524761) ^ 1428262380 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856524761) ^ 952174920 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856524761) ^ 571304952 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856524761) ^ 92145960 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856524761) ^ 11160 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3056236231 : Nat.Prime 3056236231 := by
  apply lucas_primality 3056236231 (3 : ZMod 3056236231)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (1050253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (1050253, 1)] : List FactorBlock).map factorBlockValue).prod) = 3056236231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_97
      · exact prime_seventyThreeBS_1050253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3056236231) ^ 1528118115 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3056236231) ^ 1018745410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3056236231) ^ 611247246 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3056236231) ^ 31507590 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3056236231) ^ 2910 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3306983747 : Nat.Prime 3306983747 := by
  apply lucas_primality 3306983747 (5 : ZMod 3306983747)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (6535541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (6535541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3306983747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_6535541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3306983747) ^ 1653491873 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3306983747) ^ 300634886 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3306983747) ^ 143781902 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3306983747) ^ 506 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3575521459 : Nat.Prime 3575521459 := by
  apply lucas_primality 3575521459 (2 : ZMod 3575521459)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (1319, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (1319, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3575521459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_73
      · exact prime_seventyThreeBS_1319
      · exact prime_seventyThreeBS_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3575521459) ^ 1787760729 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3575521459) ^ 1191840486 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3575521459) ^ 48979746 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3575521459) ^ 2710782 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3575521459) ^ 1733166 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3630597013 : Nat.Prime 3630597013 := by
  apply lucas_primality 3630597013 (2 : ZMod 3630597013)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (23, 1), (208799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (23, 1), (208799, 1)] : List FactorBlock).map factorBlockValue).prod) = 3630597013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_208799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3630597013) ^ 1815298506 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630597013) ^ 1210199004 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630597013) ^ 518656716 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630597013) ^ 157852044 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630597013) ^ 17388 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3665883409 : Nat.Prime 3665883409 := by
  apply lucas_primality 3665883409 (7 : ZMod 3665883409)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (19, 1), (365419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (19, 1), (365419, 1)] : List FactorBlock).map factorBlockValue).prod) = 3665883409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_365419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3665883409) ^ 1832941704 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 3665883409) ^ 1221961136 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 3665883409) ^ 333262128 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 3665883409) ^ 192941232 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 3665883409) ^ 10032 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4117175143 : Nat.Prime 4117175143 := by
  apply lucas_primality 4117175143 (3 : ZMod 4117175143)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (686195857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (686195857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4117175143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_686195857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4117175143) ^ 2058587571 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4117175143) ^ 1372391714 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4117175143) ^ 6 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4619917403 : Nat.Prime 4619917403 := by
  apply lucas_primality 4619917403 (2 : ZMod 4619917403)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1699, 1), (59113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1699, 1), (59113, 1)] : List FactorBlock).map factorBlockValue).prod) = 4619917403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_1699
      · exact prime_seventyThreeBS_59113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4619917403) ^ 2309958701 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4619917403) ^ 200865974 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4619917403) ^ 2719198 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4619917403) ^ 78154 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4908091159 : Nat.Prime 4908091159 := by
  apply lucas_primality 4908091159 (11 : ZMod 4908091159)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (10098953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (10098953, 1)] : List FactorBlock).map factorBlockValue).prod) = 4908091159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_10098953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4908091159) ^ 2454045579 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4908091159) ^ 1636030386 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4908091159) ^ 486 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4959533237 : Nat.Prime 4959533237 := by
  apply lucas_primality 4959533237 (3 : ZMod 4959533237)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (661, 1), (38281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (661, 1), (38281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4959533237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_661
      · exact prime_seventyThreeBS_38281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4959533237) ^ 2479766618 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4959533237) ^ 708504748 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4959533237) ^ 7503076 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4959533237) ^ 129556 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5251752293 : Nat.Prime 5251752293 := by
  apply lucas_primality 5251752293 (2 : ZMod 5251752293)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (113, 1), (139987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (113, 1), (139987, 1)] : List FactorBlock).map factorBlockValue).prod) = 5251752293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_83
      · exact prime_seventyThreeBS_113
      · exact prime_seventyThreeBS_139987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5251752293) ^ 2625876146 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5251752293) ^ 63274124 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5251752293) ^ 46475684 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5251752293) ^ 37516 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5525144411 : Nat.Prime 5525144411 := by
  apply lucas_primality 5525144411 (6 : ZMod 5525144411)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (24022367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (24022367, 1)] : List FactorBlock).map factorBlockValue).prod) = 5525144411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_24022367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5525144411) ^ 2762572205 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5525144411) ^ 1105028882 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5525144411) ^ 240223670 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5525144411) ^ 230 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6168426749 : Nat.Prime 6168426749 := by
  apply lucas_primality 6168426749 (2 : ZMod 6168426749)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (191, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (191, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) = 6168426749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_191
      · exact prime_seventyThreeBS_23677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6168426749) ^ 3084213374 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168426749) ^ 560766068 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168426749) ^ 198981508 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168426749) ^ 32295428 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168426749) ^ 260524 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6669992293 : Nat.Prime 6669992293 := by
  apply lucas_primality 6669992293 (2 : ZMod 6669992293)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (555832691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (555832691, 1)] : List FactorBlock).map factorBlockValue).prod) = 6669992293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_555832691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6669992293) ^ 3334996146 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6669992293) ^ 2223330764 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6669992293) ^ 12 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6869869319 : Nat.Prime 6869869319 := by
  apply lucas_primality 6869869319 (11 : ZMod 6869869319)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (264225743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (264225743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6869869319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_264225743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 6869869319) ^ 3434934659 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6869869319) ^ 528451486 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6869869319) ^ 26 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6981604429 : Nat.Prime 6981604429 := by
  apply lucas_primality 6981604429 (2 : ZMod 6981604429)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (7009643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (7009643, 1)] : List FactorBlock).map factorBlockValue).prod) = 6981604429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_83
      · exact prime_seventyThreeBS_7009643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6981604429) ^ 3490802214 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6981604429) ^ 2327201476 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6981604429) ^ 84115716 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6981604429) ^ 996 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_7803196399 : Nat.Prime 7803196399 := by
  apply lucas_primality 7803196399 (3 : ZMod 7803196399)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (197, 1), (244507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (197, 1), (244507, 1)] : List FactorBlock).map factorBlockValue).prod) = 7803196399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_197
      · exact prime_seventyThreeBS_244507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7803196399) ^ 3901598199 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7803196399) ^ 2601065466 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7803196399) ^ 39610134 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7803196399) ^ 31914 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_8874324799 : Nat.Prime 8874324799 := by
  apply lucas_primality 8874324799 (3 : ZMod 8874324799)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (7507889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (7507889, 1)] : List FactorBlock).map factorBlockValue).prod) = 8874324799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_197
      · exact prime_seventyThreeBS_7507889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8874324799) ^ 4437162399 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8874324799) ^ 2958108266 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8874324799) ^ 45047334 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8874324799) ^ 1182 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_9926377759 : Nat.Prime 9926377759 := by
  apply lucas_primality 9926377759 (15 : ZMod 9926377759)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (2949013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (2949013, 1)] : List FactorBlock).map factorBlockValue).prod) = 9926377759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_2949013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 9926377759) ^ 4963188879 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 9926377759) ^ 3308792586 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 9926377759) ^ 902397978 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 9926377759) ^ 583904574 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 9926377759) ^ 3366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_11279222099 : Nat.Prime 11279222099 := by
  apply lucas_primality 11279222099 (2 : ZMod 11279222099)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (137551489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (137551489, 1)] : List FactorBlock).map factorBlockValue).prod) = 11279222099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_137551489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11279222099) ^ 5639611049 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11279222099) ^ 275102978 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11279222099) ^ 82 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_14953249669 : Nat.Prime 14953249669 := by
  apply lucas_primality 14953249669 (2 : ZMod 14953249669)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (6271, 1), (28387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (6271, 1), (28387, 1)] : List FactorBlock).map factorBlockValue).prod) = 14953249669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_6271
      · exact prime_seventyThreeBS_28387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14953249669) ^ 7476624834 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 14953249669) ^ 4984416556 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 14953249669) ^ 2136178524 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 14953249669) ^ 2384508 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 14953249669) ^ 526764 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_17376365689 : Nat.Prime 17376365689 := by
  apply lucas_primality 17376365689 (13 : ZMod 17376365689)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (5983597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (5983597, 1)] : List FactorBlock).map factorBlockValue).prod) = 17376365689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_5983597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 17376365689) ^ 8688182844 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 17376365689) ^ 5792121896 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 17376365689) ^ 1579669608 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 17376365689) ^ 2904 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_18194372639 : Nat.Prime 18194372639 := by
  apply lucas_primality 18194372639 (7 : ZMod 18194372639)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (397, 1), (103687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (397, 1), (103687, 1)] : List FactorBlock).map factorBlockValue).prod) = 18194372639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_397
      · exact prime_seventyThreeBS_103687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18194372639) ^ 9097186319 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 18194372639) ^ 1399567126 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 18194372639) ^ 1070257214 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 18194372639) ^ 45829654 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 18194372639) ^ 175474 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_19505859949 : Nat.Prime 19505859949 := by
  apply lucas_primality 19505859949 (2 : ZMod 19505859949)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (14644039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (14644039, 1)] : List FactorBlock).map factorBlockValue).prod) = 19505859949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_37
      · exact prime_seventyThreeBS_14644039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19505859949) ^ 9752929974 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19505859949) ^ 6501953316 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19505859949) ^ 527185404 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19505859949) ^ 1332 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_22071119377 : Nat.Prime 22071119377 := by
  apply lucas_primality 22071119377 (5 : ZMod 22071119377)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (20479, 1), (22453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (20479, 1), (22453, 1)] : List FactorBlock).map factorBlockValue).prod) = 22071119377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_20479
      · exact prime_seventyThreeBS_22453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22071119377) ^ 11035559688 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 22071119377) ^ 7357039792 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 22071119377) ^ 1077744 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 22071119377) ^ 982992 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_23929739147 : Nat.Prime 23929739147 := by
  apply lucas_primality 23929739147 (2 : ZMod 23929739147)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (56705543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (56705543, 1)] : List FactorBlock).map factorBlockValue).prod) = 23929739147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_211
      · exact prime_seventyThreeBS_56705543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23929739147) ^ 11964869573 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23929739147) ^ 113411086 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23929739147) ^ 422 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_24068298941 : Nat.Prime 24068298941 := by
  apply lucas_primality 24068298941 (2 : ZMod 24068298941)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (23, 1), (31, 1), (241117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (23, 1), (31, 1), (241117, 1)] : List FactorBlock).map factorBlockValue).prod) = 24068298941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_241117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24068298941) ^ 12034149470 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24068298941) ^ 4813659788 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24068298941) ^ 3438328420 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24068298941) ^ 1046447780 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24068298941) ^ 776396740 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24068298941) ^ 99820 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_24472934063 : Nat.Prime 24472934063 := by
  apply lucas_primality 24472934063 (5 : ZMod 24472934063)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (421947139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (421947139, 1)] : List FactorBlock).map factorBlockValue).prod) = 24472934063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_421947139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24472934063) ^ 12236467031 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24472934063) ^ 843894278 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24472934063) ^ 58 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_24703050859 : Nat.Prime 24703050859 := by
  apply lucas_primality 24703050859 (2 : ZMod 24703050859)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4117175143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4117175143, 1)] : List FactorBlock).map factorBlockValue).prod) = 24703050859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_4117175143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24703050859) ^ 12351525429 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24703050859) ^ 8234350286 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24703050859) ^ 6 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_35497299197 : Nat.Prime 35497299197 := by
  apply lucas_primality 35497299197 (2 : ZMod 35497299197)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8874324799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8874324799, 1)] : List FactorBlock).map factorBlockValue).prod) = 35497299197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_8874324799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35497299197) ^ 17748649598 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 35497299197) ^ 4 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_45702386731 : Nat.Prime 45702386731 := by
  apply lucas_primality 45702386731 (7 : ZMod 45702386731)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (29, 1)] : List FactorBlock).map factorBlockValue).prod) = 45702386731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_29
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45702386731) ^ 22851193365 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 15234128910 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 9140477346 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 6528912390 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 4154762430 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 3515568210 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 2688375690 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 45702386731) ^ 1575944370 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_48668656717 : Nat.Prime 48668656717 := by
  apply lucas_primality 48668656717 (5 : ZMod 48668656717)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (283, 1), (4777057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (283, 1), (4777057, 1)] : List FactorBlock).map factorBlockValue).prod) = 48668656717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_283
      · exact prime_seventyThreeBS_4777057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48668656717) ^ 24334328358 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 48668656717) ^ 16222885572 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 48668656717) ^ 171974052 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 48668656717) ^ 10188 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_50281312307 : Nat.Prime 50281312307 := by
  apply lucas_primality 50281312307 (2 : ZMod 50281312307)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24677, 1), (1018789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24677, 1), (1018789, 1)] : List FactorBlock).map factorBlockValue).prod) = 50281312307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_24677
      · exact prime_seventyThreeBS_1018789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50281312307) ^ 25140656153 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 50281312307) ^ 2037578 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 50281312307) ^ 49354 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_54780975107 : Nat.Prime 54780975107 := by
  apply lucas_primality 54780975107 (2 : ZMod 54780975107)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (191541871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (191541871, 1)] : List FactorBlock).map factorBlockValue).prod) = 54780975107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_191541871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54780975107) ^ 27390487553 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 54780975107) ^ 4980088646 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 54780975107) ^ 4213921162 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 54780975107) ^ 286 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_63779700889 : Nat.Prime 63779700889 := by
  apply lucas_primality 63779700889 (13 : ZMod 63779700889)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (295276393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (295276393, 1)] : List FactorBlock).map factorBlockValue).prod) = 63779700889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_295276393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 63779700889) ^ 31889850444 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 63779700889) ^ 21259900296 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 63779700889) ^ 216 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_74603545033 : Nat.Prime 74603545033 := by
  apply lucas_primality 74603545033 (5 : ZMod 74603545033)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (431, 1), (7212253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (431, 1), (7212253, 1)] : List FactorBlock).map factorBlockValue).prod) = 74603545033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_431
      · exact prime_seventyThreeBS_7212253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 74603545033) ^ 37301772516 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 74603545033) ^ 24867848344 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 74603545033) ^ 173094072 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 74603545033) ^ 10344 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_86322885053 : Nat.Prime 86322885053 := by
  apply lucas_primality 86322885053 (2 : ZMod 86322885053)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (70295509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (70295509, 1)] : List FactorBlock).map factorBlockValue).prod) = 86322885053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_307
      · exact prime_seventyThreeBS_70295509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86322885053) ^ 43161442526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 86322885053) ^ 281182036 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 86322885053) ^ 1228 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_92398348061 : Nat.Prime 92398348061 := by
  apply lucas_primality 92398348061 (2 : ZMod 92398348061)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4619917403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4619917403, 1)] : List FactorBlock).map factorBlockValue).prod) = 92398348061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_4619917403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92398348061) ^ 46199174030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 92398348061) ^ 18479669612 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 92398348061) ^ 20 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_93638356789 : Nat.Prime 93638356789 := by
  apply lucas_primality 93638356789 (2 : ZMod 93638356789)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7803196399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7803196399, 1)] : List FactorBlock).map factorBlockValue).prod) = 93638356789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7803196399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93638356789) ^ 46819178394 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93638356789) ^ 31212785596 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 93638356789) ^ 12 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_102180570803 : Nat.Prime 102180570803 := by
  apply lucas_primality 102180570803 (2 : ZMod 102180570803)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4663, 1), (10956527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4663, 1), (10956527, 1)] : List FactorBlock).map factorBlockValue).prod) = 102180570803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_4663
      · exact prime_seventyThreeBS_10956527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 102180570803) ^ 51090285401 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 102180570803) ^ 21913054 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 102180570803) ^ 9326 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_109933054339 : Nat.Prime 109933054339 := by
  apply lucas_primality 109933054339 (2 : ZMod 109933054339)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (1009, 1), (255757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (1009, 1), (255757, 1)] : List FactorBlock).map factorBlockValue).prod) = 109933054339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_71
      · exact prime_seventyThreeBS_1009
      · exact prime_seventyThreeBS_255757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 109933054339) ^ 54966527169 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 109933054339) ^ 36644351446 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 109933054339) ^ 1548352878 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 109933054339) ^ 108952482 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 109933054339) ^ 429834 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_113775967273 : Nat.Prime 113775967273 := by
  apply lucas_primality 113775967273 (5 : ZMod 113775967273)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (41, 1), (419, 1), (25087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (41, 1), (419, 1), (25087, 1)] : List FactorBlock).map factorBlockValue).prod) = 113775967273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_419
      · exact prime_seventyThreeBS_25087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 113775967273) ^ 56887983636 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 113775967273) ^ 37925322424 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 113775967273) ^ 10343269752 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 113775967273) ^ 2775023592 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 113775967273) ^ 271541688 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 113775967273) ^ 4535256 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_122543507881 : Nat.Prime 122543507881 := by
  apply lucas_primality 122543507881 (26 : ZMod 122543507881)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (17, 1), (6674483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (17, 1), (6674483, 1)] : List FactorBlock).map factorBlockValue).prod) = 122543507881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_6674483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 122543507881) ^ 61271753940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (26 : ZMod 122543507881) ^ 40847835960 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (26 : ZMod 122543507881) ^ 24508701576 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (26 : ZMod 122543507881) ^ 7208441640 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (26 : ZMod 122543507881) ^ 18360 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_123598032133 : Nat.Prime 123598032133 := by
  apply lucas_primality 123598032133 (6 : ZMod 123598032133)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (15442033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (15442033, 1)] : List FactorBlock).map factorBlockValue).prod) = 123598032133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_15442033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 123598032133) ^ 61799016066 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 123598032133) ^ 41199344044 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 123598032133) ^ 5373827484 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 123598032133) ^ 4262001108 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 123598032133) ^ 8004 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_129066759383 : Nat.Prime 129066759383 := by
  apply lucas_primality 129066759383 (5 : ZMod 129066759383)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (255072647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (255072647, 1)] : List FactorBlock).map factorBlockValue).prod) = 129066759383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_255072647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129066759383) ^ 64533379691 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 129066759383) ^ 11733341762 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 129066759383) ^ 5611598234 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 129066759383) ^ 506 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_152274982579 : Nat.Prime 152274982579 := by
  apply lucas_primality 152274982579 (2 : ZMod 152274982579)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (378793489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (378793489, 1)] : List FactorBlock).map factorBlockValue).prod) = 152274982579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_67
      · exact prime_seventyThreeBS_378793489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152274982579) ^ 76137491289 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 152274982579) ^ 50758327526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 152274982579) ^ 2272760934 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 152274982579) ^ 402 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_156762043729 : Nat.Prime 156762043729 := by
  apply lucas_primality 156762043729 (13 : ZMod 156762043729)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (55353829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (55353829, 1)] : List FactorBlock).map factorBlockValue).prod) = 156762043729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_55353829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 156762043729) ^ 78381021864 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 156762043729) ^ 52254014576 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 156762043729) ^ 2656983792 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 156762043729) ^ 2832 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_271602814349 : Nat.Prime 271602814349 := by
  apply lucas_primality 271602814349 (2 : ZMod 271602814349)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 1), (47, 1), (1259543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 1), (47, 1), (1259543, 1)] : List FactorBlock).map factorBlockValue).prod) = 271602814349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_37
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_1259543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271602814349) ^ 135801407174 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 271602814349) ^ 8761381108 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 271602814349) ^ 7340616604 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 271602814349) ^ 5778783284 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 271602814349) ^ 215636 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_353596941947 : Nat.Prime 353596941947 := by
  apply lucas_primality 353596941947 (2 : ZMod 353596941947)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (26161, 1), (218003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (26161, 1), (218003, 1)] : List FactorBlock).map factorBlockValue).prod) = 353596941947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_26161
      · exact prime_seventyThreeBS_218003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 353596941947) ^ 176798470973 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 353596941947) ^ 11406352966 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 353596941947) ^ 13516186 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 353596941947) ^ 1621982 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_364464716383 : Nat.Prime 364464716383 := by
  apply lucas_primality 364464716383 (5 : ZMod 364464716383)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (313, 1), (4976171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (313, 1), (4976171, 1)] : List FactorBlock).map factorBlockValue).prod) = 364464716383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_313
      · exact prime_seventyThreeBS_4976171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 364464716383) ^ 182232358191 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 364464716383) ^ 121488238794 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 364464716383) ^ 28035747414 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 364464716383) ^ 1164424014 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 364464716383) ^ 73242 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_403650820189 : Nat.Prime 403650820189 := by
  apply lucas_primality 403650820189 (14 : ZMod 403650820189)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (145617179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (145617179, 1)] : List FactorBlock).map factorBlockValue).prod) = 403650820189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_145617179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 403650820189) ^ 201825410094 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 403650820189) ^ 134550273396 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 403650820189) ^ 57664402884 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 403650820189) ^ 36695529108 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 403650820189) ^ 2772 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_417066184057 : Nat.Prime 417066184057 := by
  apply lucas_primality 417066184057 (7 : ZMod 417066184057)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (809, 1), (21480541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (809, 1), (21480541, 1)] : List FactorBlock).map factorBlockValue).prod) = 417066184057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_809
      · exact prime_seventyThreeBS_21480541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 417066184057) ^ 208533092028 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 417066184057) ^ 139022061352 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 417066184057) ^ 515532984 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 417066184057) ^ 19416 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_586846214497 : Nat.Prime 586846214497 := by
  apply lucas_primality 586846214497 (15 : ZMod 586846214497)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (317, 1), (6427951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (317, 1), (6427951, 1)] : List FactorBlock).map factorBlockValue).prod) = 586846214497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_317
      · exact prime_seventyThreeBS_6427951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 586846214497) ^ 293423107248 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 586846214497) ^ 195615404832 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 586846214497) ^ 1851249888 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 586846214497) ^ 91296 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_838028113831 : Nat.Prime 838028113831 := by
  apply lucas_primality 838028113831 (3 : ZMod 838028113831)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (523, 1), (2207, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (523, 1), (2207, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) = 838028113831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_523
      · exact prime_seventyThreeBS_2207
      · exact prime_seventyThreeBS_2689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 838028113831) ^ 419014056915 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 838028113831) ^ 279342704610 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 838028113831) ^ 167605622766 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 838028113831) ^ 1602348210 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 838028113831) ^ 379713690 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 838028113831) ^ 311650470 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_841890307099 : Nat.Prime 841890307099 := by
  apply lucas_primality 841890307099 (2 : ZMod 841890307099)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6791, 1), (20661913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6791, 1), (20661913, 1)] : List FactorBlock).map factorBlockValue).prod) = 841890307099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_6791
      · exact prime_seventyThreeBS_20661913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 841890307099) ^ 420945153549 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 841890307099) ^ 280630102366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 841890307099) ^ 123971478 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 841890307099) ^ 40746 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1333084971583 : Nat.Prime 1333084971583 := by
  apply lucas_primality 1333084971583 (3 : ZMod 1333084971583)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (271283063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (271283063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1333084971583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_271283063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1333084971583) ^ 666542485791 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333084971583) ^ 444361657194 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333084971583) ^ 190440710226 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333084971583) ^ 102544997814 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1333084971583) ^ 4914 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1384666981169 : Nat.Prime 1384666981169 := by
  apply lucas_primality 1384666981169 (3 : ZMod 1384666981169)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (25583, 1), (3382781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (25583, 1), (3382781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384666981169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_25583
      · exact prime_seventyThreeBS_3382781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1384666981169) ^ 692333490584 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1384666981169) ^ 54124496 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1384666981169) ^ 409328 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1387535452829 : Nat.Prime 1387535452829 := by
  apply lucas_primality 1387535452829 (2 : ZMod 1387535452829)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (727, 1), (68163463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (727, 1), (68163463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1387535452829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_727
      · exact prime_seventyThreeBS_68163463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1387535452829) ^ 693767726414 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387535452829) ^ 198219350404 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387535452829) ^ 1908576964 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387535452829) ^ 20356 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1656528889451 : Nat.Prime 1656528889451 := by
  apply lucas_primality 1656528889451 (6 : ZMod 1656528889451)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (397, 1), (4908961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (397, 1), (4908961, 1)] : List FactorBlock).map factorBlockValue).prod) = 1656528889451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_397
      · exact prime_seventyThreeBS_4908961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1656528889451) ^ 828264444725 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656528889451) ^ 331305777890 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656528889451) ^ 97442875850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656528889451) ^ 4172616850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1656528889451) ^ 337450 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2080909023097 : Nat.Prime 2080909023097 := by
  apply lucas_primality 2080909023097 (5 : ZMod 2080909023097)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (37, 1), (1303, 1), (78193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (37, 1), (1303, 1), (78193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2080909023097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_37
      · exact prime_seventyThreeBS_1303
      · exact prime_seventyThreeBS_78193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2080909023097) ^ 1040454511548 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2080909023097) ^ 693636341032 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2080909023097) ^ 90474305352 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2080909023097) ^ 56240784408 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2080909023097) ^ 1597013832 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2080909023097) ^ 26612472 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2317990159621 : Nat.Prime 2317990159621 := by
  apply lucas_primality 2317990159621 (2 : ZMod 2317990159621)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (101, 1), (863, 1), (147743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (101, 1), (863, 1), (147743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2317990159621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_101
      · exact prime_seventyThreeBS_863
      · exact prime_seventyThreeBS_147743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2317990159621) ^ 1158995079810 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317990159621) ^ 772663386540 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317990159621) ^ 463598031924 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317990159621) ^ 22950397620 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317990159621) ^ 2685967740 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317990159621) ^ 15689340 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3102256515871 : Nat.Prime 3102256515871 := by
  apply lucas_primality 3102256515871 (3 : ZMod 3102256515871)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (44248417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (44248417, 1)] : List FactorBlock).map factorBlockValue).prod) = 3102256515871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_44248417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3102256515871) ^ 1551128257935 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3102256515871) ^ 1034085505290 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3102256515871) ^ 620451303174 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3102256515871) ^ 163276658730 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3102256515871) ^ 75664793070 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3102256515871) ^ 70110 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3113517746369 : Nat.Prime 3113517746369 := by
  apply lucas_primality 3113517746369 (3 : ZMod 3113517746369)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (53, 1), (48310541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (53, 1), (48310541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113517746369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_53
      · exact prime_seventyThreeBS_48310541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3113517746369) ^ 1556758873184 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113517746369) ^ 163869355072 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113517746369) ^ 58745617856 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113517746369) ^ 64448 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3154220823431 : Nat.Prime 3154220823431 := by
  apply lucas_primality 3154220823431 (13 : ZMod 3154220823431)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3343, 1), (9547, 1), (9883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3343, 1), (9547, 1), (9883, 1)] : List FactorBlock).map factorBlockValue).prod) = 3154220823431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_3343
      · exact prime_seventyThreeBS_9547
      · exact prime_seventyThreeBS_9883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3154220823431) ^ 1577110411715 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 3154220823431) ^ 630844164686 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 3154220823431) ^ 943530010 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 3154220823431) ^ 330388690 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 3154220823431) ^ 319156210 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4032477173051 : Nat.Prime 4032477173051 := by
  apply lucas_primality 4032477173051 (6 : ZMod 4032477173051)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3557, 1), (22673473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3557, 1), (22673473, 1)] : List FactorBlock).map factorBlockValue).prod) = 4032477173051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_3557
      · exact prime_seventyThreeBS_22673473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4032477173051) ^ 2016238586525 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4032477173051) ^ 806495434610 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4032477173051) ^ 1133673650 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4032477173051) ^ 177850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4363311062447 : Nat.Prime 4363311062447 := by
  apply lucas_primality 4363311062447 (5 : ZMod 4363311062447)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1277, 1), (244060357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1277, 1), (244060357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4363311062447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_1277
      · exact prime_seventyThreeBS_244060357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4363311062447) ^ 2181655531223 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4363311062447) ^ 623330151778 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4363311062447) ^ 3416844998 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4363311062447) ^ 17878 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5299862567743 : Nat.Prime 5299862567743 := by
  apply lucas_primality 5299862567743 (3 : ZMod 5299862567743)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7933, 1), (37115443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7933, 1), (37115443, 1)] : List FactorBlock).map factorBlockValue).prod) = 5299862567743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7933
      · exact prime_seventyThreeBS_37115443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5299862567743) ^ 2649931283871 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5299862567743) ^ 1766620855914 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5299862567743) ^ 668077974 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5299862567743) ^ 142794 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5382970440907 : Nat.Prime 5382970440907 := by
  apply lucas_primality 5382970440907 (11 : ZMod 5382970440907)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (509, 1), (29874521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (509, 1), (29874521, 1)] : List FactorBlock).map factorBlockValue).prod) = 5382970440907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_509
      · exact prime_seventyThreeBS_29874521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5382970440907) ^ 2691485220453 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5382970440907) ^ 1794323480302 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5382970440907) ^ 91236787134 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5382970440907) ^ 10575580434 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5382970440907) ^ 180186 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6309006137857 : Nat.Prime 6309006137857 := by
  apply lucas_primality 6309006137857 (5 : ZMod 6309006137857)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (19, 2), (3792637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (19, 2), (3792637, 1)] : List FactorBlock).map factorBlockValue).prod) = 6309006137857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_3792637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6309006137857) ^ 3154503068928 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309006137857) ^ 2103002045952 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309006137857) ^ 332052954624 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6309006137857) ^ 1663488 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6607897489603 : Nat.Prime 6607897489603 := by
  apply lucas_primality 6607897489603 (2 : ZMod 6607897489603)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (283, 1), (13003, 1), (99761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (283, 1), (13003, 1), (99761, 1)] : List FactorBlock).map factorBlockValue).prod) = 6607897489603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_283
      · exact prime_seventyThreeBS_13003
      · exact prime_seventyThreeBS_99761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6607897489603) ^ 3303948744801 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6607897489603) ^ 2202632496534 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6607897489603) ^ 23349461094 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6607897489603) ^ 508182534 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6607897489603) ^ 66237282 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6824591083169 : Nat.Prime 6824591083169 := by
  apply lucas_primality 6824591083169 (3 : ZMod 6824591083169)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (103, 1), (121798099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (103, 1), (121798099, 1)] : List FactorBlock).map factorBlockValue).prod) = 6824591083169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_103
      · exact prime_seventyThreeBS_121798099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6824591083169) ^ 3412295541584 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6824591083169) ^ 401446534304 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6824591083169) ^ 66258165856 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6824591083169) ^ 56032 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_8380281138311 : Nat.Prime 8380281138311 := by
  apply lucas_primality 8380281138311 (11 : ZMod 8380281138311)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (838028113831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (838028113831, 1)] : List FactorBlock).map factorBlockValue).prod) = 8380281138311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_838028113831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 8380281138311) ^ 4190140569155 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8380281138311) ^ 1676056227662 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8380281138311) ^ 10 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_9509600182729 : Nat.Prime 9509600182729 := by
  apply lucas_primality 9509600182729 (7 : ZMod 9509600182729)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (823, 1), (14797, 1), (32537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (823, 1), (14797, 1), (32537, 1)] : List FactorBlock).map factorBlockValue).prod) = 9509600182729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_823
      · exact prime_seventyThreeBS_14797
      · exact prime_seventyThreeBS_32537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9509600182729) ^ 4754800091364 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9509600182729) ^ 3169866727576 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9509600182729) ^ 11554799736 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9509600182729) ^ 642670824 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9509600182729) ^ 292270344 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_10563231860947 : Nat.Prime 10563231860947 := by
  apply lucas_primality 10563231860947 (3 : ZMod 10563231860947)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (586846214497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (586846214497, 1)] : List FactorBlock).map factorBlockValue).prod) = 10563231860947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_586846214497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10563231860947) ^ 5281615930473 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10563231860947) ^ 3521077286982 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10563231860947) ^ 18 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_10674772673947 : Nat.Prime 10674772673947 := by
  apply lucas_primality 10674772673947 (3 : ZMod 10674772673947)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (93638356789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (93638356789, 1)] : List FactorBlock).map factorBlockValue).prod) = 10674772673947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_93638356789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10674772673947) ^ 5337386336973 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10674772673947) ^ 3558257557982 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10674772673947) ^ 561830140734 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10674772673947) ^ 114 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_13379170393811 : Nat.Prime 13379170393811 := by
  apply lucas_primality 13379170393811 (2 : ZMod 13379170393811)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (15667, 1), (6569011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (15667, 1), (6569011, 1)] : List FactorBlock).map factorBlockValue).prod) = 13379170393811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_15667
      · exact prime_seventyThreeBS_6569011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13379170393811) ^ 6689585196905 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13379170393811) ^ 2675834078762 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13379170393811) ^ 1029166953370 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13379170393811) ^ 853971430 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13379170393811) ^ 2036710 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_13649182166339 : Nat.Prime 13649182166339 := by
  apply lucas_primality 13649182166339 (2 : ZMod 13649182166339)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6824591083169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6824591083169, 1)] : List FactorBlock).map factorBlockValue).prod) = 13649182166339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_6824591083169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13649182166339) ^ 6824591083169 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13649182166339) ^ 2 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_24189838675307 : Nat.Prime 24189838675307 := by
  apply lucas_primality 24189838675307 (2 : ZMod 24189838675307)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (417066184057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (417066184057, 1)] : List FactorBlock).map factorBlockValue).prod) = 24189838675307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_417066184057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24189838675307) ^ 12094919337653 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24189838675307) ^ 834132368114 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24189838675307) ^ 58 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_28815201020849 : Nat.Prime 28815201020849 := by
  apply lucas_primality 28815201020849 (3 : ZMod 28815201020849)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (160357, 1), (1020989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (160357, 1), (1020989, 1)] : List FactorBlock).map factorBlockValue).prod) = 28815201020849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_160357
      · exact prime_seventyThreeBS_1020989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28815201020849) ^ 14407600510424 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28815201020849) ^ 2619563729168 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28815201020849) ^ 179694064 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 28815201020849) ^ 28222832 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_30755541062531 : Nat.Prime 30755541062531 := by
  apply lucas_primality 30755541062531 (2 : ZMod 30755541062531)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3557, 1), (864648329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3557, 1), (864648329, 1)] : List FactorBlock).map factorBlockValue).prod) = 30755541062531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_3557
      · exact prime_seventyThreeBS_864648329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30755541062531) ^ 15377770531265 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30755541062531) ^ 6151108212506 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30755541062531) ^ 8646483290 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 30755541062531) ^ 35570 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_31799175406459 : Nat.Prime 31799175406459 := by
  apply lucas_primality 31799175406459 (3 : ZMod 31799175406459)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5299862567743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5299862567743, 1)] : List FactorBlock).map factorBlockValue).prod) = 31799175406459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5299862567743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31799175406459) ^ 15899587703229 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31799175406459) ^ 10599725135486 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31799175406459) ^ 6 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_33929382163951 : Nat.Prime 33929382163951 := by
  apply lucas_primality 33929382163951 (6 : ZMod 33929382163951)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 1), (13, 1), (113, 1), (2444119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 1), (13, 1), (113, 1), (2444119, 1)] : List FactorBlock).map factorBlockValue).prod) = 33929382163951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_113
      · exact prime_seventyThreeBS_2444119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33929382163951) ^ 16964691081975 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 11309794054650 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 6785876432790 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 4847054594850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 2609952474150 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 300260019150 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 33929382163951) ^ 13882050 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_34988612772769 : Nat.Prime 34988612772769 := by
  apply lucas_primality 34988612772769 (11 : ZMod 34988612772769)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (364464716383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (364464716383, 1)] : List FactorBlock).map factorBlockValue).prod) = 34988612772769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_364464716383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 34988612772769) ^ 17494306386384 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 34988612772769) ^ 11662870924256 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 34988612772769) ^ 96 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_35442562517281 : Nat.Prime 35442562517281 := by
  apply lucas_primality 35442562517281 (14 : ZMod 35442562517281)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (89, 1), (227, 1), (406093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (89, 1), (227, 1), (406093, 1)] : List FactorBlock).map factorBlockValue).prod) = 35442562517281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_89
      · exact prime_seventyThreeBS_227
      · exact prime_seventyThreeBS_406093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 35442562517281) ^ 17721281258640 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 35442562517281) ^ 11814187505760 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 35442562517281) ^ 7088512503456 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 35442562517281) ^ 398231039520 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 35442562517281) ^ 156134636640 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (14 : ZMod 35442562517281) ^ 87276960 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_106747726739471 : Nat.Prime 106747726739471 := by
  apply lucas_primality 106747726739471 (11 : ZMod 106747726739471)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10674772673947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10674772673947, 1)] : List FactorBlock).map factorBlockValue).prod) = 106747726739471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_10674772673947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 106747726739471) ^ 53373863369735 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 106747726739471) ^ 21349545347894 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 106747726739471) ^ 10 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_136915656660259 : Nat.Prime 136915656660259 := by
  apply lucas_primality 136915656660259 (2 : ZMod 136915656660259)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (277, 1), (547, 1), (241739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (277, 1), (547, 1), (241739, 1)] : List FactorBlock).map factorBlockValue).prod) = 136915656660259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_89
      · exact prime_seventyThreeBS_277
      · exact prime_seventyThreeBS_547
      · exact prime_seventyThreeBS_241739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 136915656660259) ^ 68457828330129 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 45638552220086 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 19559379522894 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 1538378164722 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 494280348954 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 250302845814 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136915656660259) ^ 566378022 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_192653905935083 : Nat.Prime 192653905935083 := by
  apply lucas_primality 192653905935083 (2 : ZMod 192653905935083)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (490183, 1), (196512227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (490183, 1), (196512227, 1)] : List FactorBlock).map factorBlockValue).prod) = 192653905935083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_490183
      · exact prime_seventyThreeBS_196512227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 192653905935083) ^ 96326952967541 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192653905935083) ^ 393024454 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192653905935083) ^ 980366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_233887723413031 : Nat.Prime 233887723413031 := by
  apply lucas_primality 233887723413031 (3 : ZMod 233887723413031)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (227, 1), (279225581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (227, 1), (279225581, 1)] : List FactorBlock).map factorBlockValue).prod) = 233887723413031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_227
      · exact prime_seventyThreeBS_279225581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 233887723413031) ^ 116943861706515 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 233887723413031) ^ 77962574471010 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 233887723413031) ^ 46777544682606 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 233887723413031) ^ 5704578619830 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 233887723413031) ^ 1030342393890 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 233887723413031) ^ 837630 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_247758229738351 : Nat.Prime 247758229738351 := by
  apply lucas_primality 247758229738351 (3 : ZMod 247758229738351)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (1151, 1), (159447971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (1151, 1), (159447971, 1)] : List FactorBlock).map factorBlockValue).prod) = 247758229738351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_1151
      · exact prime_seventyThreeBS_159447971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 247758229738351) ^ 123879114869175 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 247758229738351) ^ 82586076579450 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 247758229738351) ^ 49551645947670 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 247758229738351) ^ 215254760850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 247758229738351) ^ 1553850 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_289627016865259 : Nat.Prime 289627016865259 := by
  apply lucas_primality 289627016865259 (2 : ZMod 289627016865259)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (152274982579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (152274982579, 1)] : List FactorBlock).map factorBlockValue).prod) = 289627016865259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_317
      · exact prime_seventyThreeBS_152274982579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 289627016865259) ^ 144813508432629 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 289627016865259) ^ 96542338955086 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 289627016865259) ^ 913649895474 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 289627016865259) ^ 1902 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_396426705802469 : Nat.Prime 396426705802469 := by
  apply lucas_primality 396426705802469 (2 : ZMod 396426705802469)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (103, 1), (179, 1), (1601, 1), (305231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (103, 1), (179, 1), (1601, 1), (305231, 1)] : List FactorBlock).map factorBlockValue).prod) = 396426705802469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_103
      · exact prime_seventyThreeBS_179
      · exact prime_seventyThreeBS_1601
      · exact prime_seventyThreeBS_305231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 396426705802469) ^ 198213352901234 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 396426705802469) ^ 36038791436588 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 396426705802469) ^ 3848802968956 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 396426705802469) ^ 2214674334092 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 396426705802469) ^ 247611933668 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 396426705802469) ^ 1298776028 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_406535062245817 : Nat.Prime 406535062245817 := by
  apply lucas_primality 406535062245817 (11 : ZMod 406535062245817)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (19, 1), (18194372639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (19, 1), (18194372639, 1)] : List FactorBlock).map factorBlockValue).prod) = 406535062245817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_18194372639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 406535062245817) ^ 203267531122908 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 406535062245817) ^ 135511687415272 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 406535062245817) ^ 58076437463688 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 406535062245817) ^ 21396582223464 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 406535062245817) ^ 22344 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_781274204987873 : Nat.Prime 781274204987873 := by
  apply lucas_primality 781274204987873 (3 : ZMod 781274204987873)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (841890307099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (841890307099, 1)] : List FactorBlock).map factorBlockValue).prod) = 781274204987873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_841890307099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 781274204987873) ^ 390637102493936 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 781274204987873) ^ 26940489827168 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 781274204987873) ^ 928 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_874742610508577 : Nat.Prime 874742610508577 := by
  apply lucas_primality 874742610508577 (3 : ZMod 874742610508577)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (499, 1), (54780975107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (499, 1), (54780975107, 1)] : List FactorBlock).map factorBlockValue).prod) = 874742610508577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_499
      · exact prime_seventyThreeBS_54780975107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 874742610508577) ^ 437371305254288 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 874742610508577) ^ 1752991203424 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 874742610508577) ^ 15968 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1282783880918383 : Nat.Prime 1282783880918383 := by
  apply lucas_primality 1282783880918383 (3 : ZMod 1282783880918383)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1481, 1), (2281, 1), (3203, 1), (19759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1481, 1), (2281, 1), (3203, 1), (19759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1282783880918383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1481
      · exact prime_seventyThreeBS_2281
      · exact prime_seventyThreeBS_3203
      · exact prime_seventyThreeBS_19759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1282783880918383) ^ 641391940459191 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282783880918383) ^ 427594626972794 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282783880918383) ^ 866160621822 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282783880918383) ^ 562377852222 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282783880918383) ^ 400494499194 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282783880918383) ^ 64921498098 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1733268462857161 : Nat.Prime 1733268462857161 := by
  apply lucas_primality 1733268462857161 (7 : ZMod 1733268462857161)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (607, 1), (24923, 1), (954763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (607, 1), (24923, 1), (954763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733268462857161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_607
      · exact prime_seventyThreeBS_24923
      · exact prime_seventyThreeBS_954763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1733268462857161) ^ 866634231428580 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1733268462857161) ^ 577756154285720 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1733268462857161) ^ 346653692571432 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1733268462857161) ^ 2855466989880 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1733268462857161) ^ 69544936920 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1733268462857161) ^ 1815391320 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3343543859833579 : Nat.Prime 3343543859833579 := by
  apply lucas_primality 3343543859833579 (3 : ZMod 3343543859833579)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (239, 1), (3319, 1), (78056327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (239, 1), (3319, 1), (78056327, 1)] : List FactorBlock).map factorBlockValue).prod) = 3343543859833579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_239
      · exact prime_seventyThreeBS_3319
      · exact prime_seventyThreeBS_78056327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3343543859833579) ^ 1671771929916789 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3343543859833579) ^ 1114514619944526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3343543859833579) ^ 13989723262902 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3343543859833579) ^ 1007394956262 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3343543859833579) ^ 42835014 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3551753269692059 : Nat.Prime 3551753269692059 := by
  apply lucas_primality 3551753269692059 (2 : ZMod 3551753269692059)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (18181, 1), (266151527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (18181, 1), (266151527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3551753269692059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_367
      · exact prime_seventyThreeBS_18181
      · exact prime_seventyThreeBS_266151527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3551753269692059) ^ 1775876634846029 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3551753269692059) ^ 9677801824774 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3551753269692059) ^ 195355220818 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3551753269692059) ^ 13344854 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4214141249635511 : Nat.Prime 4214141249635511 := by
  apply lucas_primality 4214141249635511 (19 : ZMod 4214141249635511)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (39857, 1), (173330363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (39857, 1), (173330363, 1)] : List FactorBlock).map factorBlockValue).prod) = 4214141249635511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_61
      · exact prime_seventyThreeBS_39857
      · exact prime_seventyThreeBS_173330363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4214141249635511) ^ 2107070624817755 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (19 : ZMod 4214141249635511) ^ 842828249927102 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (19 : ZMod 4214141249635511) ^ 69084282780910 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (19 : ZMod 4214141249635511) ^ 105731521430 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (19 : ZMod 4214141249635511) ^ 24312770 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4643428517462753 : Nat.Prime 4643428517462753 := by
  apply lucas_primality 4643428517462753 (3 : ZMod 4643428517462753)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (6309006137857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (6309006137857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4643428517462753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_6309006137857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4643428517462753) ^ 2321714258731376 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4643428517462753) ^ 201888196411424 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4643428517462753) ^ 736 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_9823114393552237 : Nat.Prime 9823114393552237 := by
  apply lucas_primality 9823114393552237 (11 : ZMod 9823114393552237)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (4032477173051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (4032477173051, 1)] : List FactorBlock).map factorBlockValue).prod) = 9823114393552237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_4032477173051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9823114393552237) ^ 4911557196776118 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 9823114393552237) ^ 3274371464517412 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 9823114393552237) ^ 1403302056221748 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 9823114393552237) ^ 338728082536284 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 9823114393552237) ^ 2436 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_13557692783891569 : Nat.Prime 13557692783891569 := by
  apply lucas_primality 13557692783891569 (7 : ZMod 13557692783891569)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (1453, 1), (14953249669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (1453, 1), (14953249669, 1)] : List FactorBlock).map factorBlockValue).prod) = 13557692783891569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_1453
      · exact prime_seventyThreeBS_14953249669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13557692783891569) ^ 6778846391945784 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 13557692783891569) ^ 4519230927963856 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 13557692783891569) ^ 1042899444914736 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 13557692783891569) ^ 9330827793456 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 13557692783891569) ^ 906672 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_25587898506513913 : Nat.Prime 25587898506513913 := by
  apply lucas_primality 25587898506513913 (7 : ZMod 25587898506513913)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (28815201020849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (28815201020849, 1)] : List FactorBlock).map factorBlockValue).prod) = 25587898506513913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_37
      · exact prime_seventyThreeBS_28815201020849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25587898506513913) ^ 12793949253256956 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 25587898506513913) ^ 8529299502171304 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 25587898506513913) ^ 691564824500376 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 25587898506513913) ^ 888 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_75311846938995983 : Nat.Prime 75311846938995983 := by
  apply lucas_primality 75311846938995983 (7 : ZMod 75311846938995983)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (233887723413031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (233887723413031, 1)] : List FactorBlock).map factorBlockValue).prod) = 75311846938995983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_233887723413031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 75311846938995983) ^ 37655923469497991 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 75311846938995983) ^ 10758835276999426 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 75311846938995983) ^ 3274428127782434 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 75311846938995983) ^ 322 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_84067326164485031 : Nat.Prime 84067326164485031 := by
  apply lucas_primality 84067326164485031 (7 : ZMod 84067326164485031)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (2939, 1), (4793, 1), (5475121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (2939, 1), (4793, 1), (5475121, 1)] : List FactorBlock).map factorBlockValue).prod) = 84067326164485031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_109
      · exact prime_seventyThreeBS_2939
      · exact prime_seventyThreeBS_4793
      · exact prime_seventyThreeBS_5475121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84067326164485031) ^ 42033663082242515 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84067326164485031) ^ 16813465232897006 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84067326164485031) ^ 771259873068670 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84067326164485031) ^ 28604057898770 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84067326164485031) ^ 17539604874710 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 84067326164485031) ^ 15354423430 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_109308517353991337 : Nat.Prime 109308517353991337 := by
  apply lucas_primality 109308517353991337 (3 : ZMod 109308517353991337)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (7963, 1), (74603545033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (7963, 1), (74603545033, 1)] : List FactorBlock).map factorBlockValue).prod) = 109308517353991337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_7963
      · exact prime_seventyThreeBS_74603545033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 109308517353991337) ^ 54654258676995668 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109308517353991337) ^ 4752544232782232 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109308517353991337) ^ 13727052286072 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109308517353991337) ^ 1465192 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_109773208642563847 : Nat.Prime 109773208642563847 := by
  apply lucas_primality 109773208642563847 (3 : ZMod 109773208642563847)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (23, 1), (251, 1), (56629, 1), (1097323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (23, 1), (251, 1), (56629, 1), (1097323, 1)] : List FactorBlock).map factorBlockValue).prod) = 109773208642563847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_251
      · exact prime_seventyThreeBS_56629
      · exact prime_seventyThreeBS_1097323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109773208642563847) ^ 54886604321281923 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 36591069547521282 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 6457247567209638 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 4772748201850602 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 437343460727346 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 1938462777774 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 109773208642563847) ^ 100037280402 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_113506105515089909 : Nat.Prime 113506105515089909 := by
  apply lucas_primality 113506105515089909 (2 : ZMod 113506105515089909)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (41243, 1), (11279222099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (41243, 1), (11279222099, 1)] : List FactorBlock).map factorBlockValue).prod) = 113506105515089909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_61
      · exact prime_seventyThreeBS_41243
      · exact prime_seventyThreeBS_11279222099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113506105515089909) ^ 56753052757544954 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 113506105515089909) ^ 1860755828116228 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 113506105515089909) ^ 2752130192156 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 113506105515089909) ^ 10063292 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_165644114185404821 : Nat.Prime 165644114185404821 := by
  apply lucas_primality 165644114185404821 (2 : ZMod 165644114185404821)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (67, 1), (1213, 1), (16603, 1), (876851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (67, 1), (1213, 1), (16603, 1), (876851, 1)] : List FactorBlock).map factorBlockValue).prod) = 165644114185404821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_67
      · exact prime_seventyThreeBS_1213
      · exact prime_seventyThreeBS_16603
      · exact prime_seventyThreeBS_876851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 165644114185404821) ^ 82822057092702410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 33128822837080964 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 23663444883629260 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 2472300211722460 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 136557390095140 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 9976758066940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 165644114185404821) ^ 188907937820 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_171692233451964787 : Nat.Prime 171692233451964787 := by
  apply lucas_primality 171692233451964787 (2 : ZMod 171692233451964787)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (136915656660259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (136915656660259, 1)] : List FactorBlock).map factorBlockValue).prod) = 171692233451964787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_136915656660259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171692233451964787) ^ 85846116725982393 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 171692233451964787) ^ 57230744483988262 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 171692233451964787) ^ 15608384859269526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 171692233451964787) ^ 9036433339577094 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 171692233451964787) ^ 1254 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_336667485971091881 : Nat.Prime 336667485971091881 := by
  apply lucas_primality 336667485971091881 (3 : ZMod 336667485971091881)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (389, 1), (135241, 1), (14544223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (389, 1), (135241, 1), (14544223, 1)] : List FactorBlock).map factorBlockValue).prod) = 336667485971091881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_389
      · exact prime_seventyThreeBS_135241
      · exact prime_seventyThreeBS_14544223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 336667485971091881) ^ 168333742985545940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 336667485971091881) ^ 67333497194218376 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 336667485971091881) ^ 30606135088281080 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 336667485971091881) ^ 865469115606920 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 336667485971091881) ^ 2489389208680 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 336667485971091881) ^ 23147849560 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_614109564156333913 : Nat.Prime 614109564156333913 := by
  apply lucas_primality 614109564156333913 (7 : ZMod 614109564156333913)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (25587898506513913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (25587898506513913, 1)] : List FactorBlock).map factorBlockValue).prod) = 614109564156333913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_25587898506513913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 614109564156333913) ^ 307054782078166956 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 614109564156333913) ^ 204703188052111304 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 614109564156333913) ^ 24 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_801339220242766801 : Nat.Prime 801339220242766801 := by
  apply lucas_primality 801339220242766801 (22 : ZMod 801339220242766801)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 1), (31799175406459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 1), (31799175406459, 1)] : List FactorBlock).map factorBlockValue).prod) = 801339220242766801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_31799175406459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 801339220242766801) ^ 400669610121383400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (22 : ZMod 801339220242766801) ^ 267113073414255600 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (22 : ZMod 801339220242766801) ^ 160267844048553360 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (22 : ZMod 801339220242766801) ^ 114477031463252400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (22 : ZMod 801339220242766801) ^ 25200 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_811860994947013309 : Nat.Prime 811860994947013309 := by
  apply lucas_primality 811860994947013309 (2 : ZMod 811860994947013309)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (61, 1), (1594063, 1), (21083911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (61, 1), (1594063, 1), (21083911, 1)] : List FactorBlock).map factorBlockValue).prod) = 811860994947013309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_61
      · exact prime_seventyThreeBS_1594063
      · exact prime_seventyThreeBS_21083911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 811860994947013309) ^ 405930497473506654 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 811860994947013309) ^ 270620331649004436 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 811860994947013309) ^ 73805544995183028 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 811860994947013309) ^ 13309196638475628 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 811860994947013309) ^ 509302954116 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 811860994947013309) ^ 38506185828 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_886944090313260557 : Nat.Prime 886944090313260557 := by
  apply lucas_primality 886944090313260557 (2 : ZMod 886944090313260557)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (3539, 1), (1333084971583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (3539, 1), (1333084971583, 1)] : List FactorBlock).map factorBlockValue).prod) = 886944090313260557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_3539
      · exact prime_seventyThreeBS_1333084971583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 886944090313260557) ^ 443472045156630278 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 886944090313260557) ^ 18871150857728948 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 886944090313260557) ^ 250619974657604 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 886944090313260557) ^ 665332 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2023642918884731201 : Nat.Prime 2023642918884731201 := by
  apply lucas_primality 2023642918884731201 (3 : ZMod 2023642918884731201)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (7, 1), (19, 1), (9509600182729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (7, 1), (19, 1), (9509600182729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2023642918884731201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_9509600182729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2023642918884731201) ^ 1011821459442365600 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2023642918884731201) ^ 404728583776946240 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2023642918884731201) ^ 289091845554961600 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2023642918884731201) ^ 106507522046564800 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2023642918884731201) ^ 212800 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2193802932572944597 : Nat.Prime 2193802932572944597 := by
  apply lucas_primality 2193802932572944597 (13 : ZMod 2193802932572944597)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (571, 1), (6197, 1), (555540613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (571, 1), (6197, 1), (555540613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2193802932572944597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_571
      · exact prime_seventyThreeBS_6197
      · exact prime_seventyThreeBS_555540613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2193802932572944597) ^ 1096901466286472298 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2193802932572944597) ^ 731267644190981532 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2193802932572944597) ^ 70767836534611116 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2193802932572944597) ^ 3842036659497276 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2193802932572944597) ^ 354010478065668 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2193802932572944597) ^ 3948951492 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3271362946754518331 : Nat.Prime 3271362946754518331 := by
  apply lucas_primality 3271362946754518331 (2 : ZMod 3271362946754518331)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (1381, 1), (1656528889451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (1381, 1), (1656528889451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3271362946754518331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_1381
      · exact prime_seventyThreeBS_1656528889451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3271362946754518331) ^ 1635681473377259165 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271362946754518331) ^ 654272589350903666 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271362946754518331) ^ 297396631523138030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271362946754518331) ^ 251643303596501410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271362946754518331) ^ 2368836311914930 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271362946754518331) ^ 1974830 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_4674335594937222073 : Nat.Prime 4674335594937222073 := by
  apply lucas_primality 4674335594937222073 (13 : ZMod 4674335594937222073)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2107873, 1), (92398348061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2107873, 1), (92398348061, 1)] : List FactorBlock).map factorBlockValue).prod) = 4674335594937222073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_2107873
      · exact prime_seventyThreeBS_92398348061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4674335594937222073) ^ 2337167797468611036 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 4674335594937222073) ^ 1558111864979074024 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 4674335594937222073) ^ 2217560353464 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 4674335594937222073) ^ 50588952 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5113591102757559239 : Nat.Prime 5113591102757559239 := by
  apply lucas_primality 5113591102757559239 (11 : ZMod 5113591102757559239)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (8231, 1), (10663, 1), (549652391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (8231, 1), (10663, 1), (549652391, 1)] : List FactorBlock).map factorBlockValue).prod) = 5113591102757559239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_53
      · exact prime_seventyThreeBS_8231
      · exact prime_seventyThreeBS_10663
      · exact prime_seventyThreeBS_549652391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5113591102757559239) ^ 2556795551378779619 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5113591102757559239) ^ 96482850995425646 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5113591102757559239) ^ 621260005194698 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5113591102757559239) ^ 479564016014026 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 5113591102757559239) ^ 9303318218 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5728540309018458901 : Nat.Prime 5728540309018458901 := by
  apply lucas_primality 5728540309018458901 (2 : ZMod 5728540309018458901)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 1), (7297, 1), (113775967273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 1), (7297, 1), (113775967273, 1)] : List FactorBlock).map factorBlockValue).prod) = 5728540309018458901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_7297
      · exact prime_seventyThreeBS_113775967273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5728540309018458901) ^ 2864270154509229450 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5728540309018458901) ^ 1909513436339486300 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5728540309018458901) ^ 1145708061803691780 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5728540309018458901) ^ 249066969957324300 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5728540309018458901) ^ 785054174183700 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5728540309018458901) ^ 50349300 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5903332434799200829 : Nat.Prime 5903332434799200829 := by
  apply lucas_primality 5903332434799200829 (6 : ZMod 5903332434799200829)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (47, 1), (1231, 1), (163861, 1), (2470957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (47, 1), (1231, 1), (163861, 1), (2470957, 1)] : List FactorBlock).map factorBlockValue).prod) = 5903332434799200829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_1231
      · exact prime_seventyThreeBS_163861
      · exact prime_seventyThreeBS_2470957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5903332434799200829) ^ 2951666217399600414 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 1967777478266400276 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 843333204971314404 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 125602817761685124 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 4795558436067588 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 36026464105548 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5903332434799200829) ^ 2389087481004 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6369624872744273359 : Nat.Prime 6369624872744273359 := by
  apply lucas_primality 6369624872744273359 (6 : ZMod 6369624872744273359)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (6673, 1), (237271, 1), (14265893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (6673, 1), (237271, 1), (14265893, 1)] : List FactorBlock).map factorBlockValue).prod) = 6369624872744273359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_6673
      · exact prime_seventyThreeBS_237271
      · exact prime_seventyThreeBS_14265893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6369624872744273359) ^ 3184812436372136679 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 6369624872744273359) ^ 2123208290914757786 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 6369624872744273359) ^ 135523933462644114 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 6369624872744273359) ^ 954536920836846 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 6369624872744273359) ^ 26845357724898 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 6369624872744273359) ^ 446493246006 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_8835509342226014671 : Nat.Prime 8835509342226014671 := by
  apply lucas_primality 8835509342226014671 (3 : ZMod 8835509342226014671)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (89, 1), (106747726739471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (89, 1), (106747726739471, 1)] : List FactorBlock).map factorBlockValue).prod) = 8835509342226014671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_89
      · exact prime_seventyThreeBS_106747726739471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8835509342226014671) ^ 4417754671113007335 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8835509342226014671) ^ 2945169780742004890 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8835509342226014671) ^ 1767101868445202934 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8835509342226014671) ^ 285016430394387570 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8835509342226014671) ^ 99275385867708030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 8835509342226014671) ^ 82770 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_10458749452596171553 : Nat.Prime 10458749452596171553 := by
  apply lucas_primality 10458749452596171553 (13 : ZMod 10458749452596171553)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (61, 1), (1129477, 1), (75297751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (61, 1), (1129477, 1), (75297751, 1)] : List FactorBlock).map factorBlockValue).prod) = 10458749452596171553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_61
      · exact prime_seventyThreeBS_1129477
      · exact prime_seventyThreeBS_75297751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10458749452596171553) ^ 5229374726298085776 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 10458749452596171553) ^ 3486249817532057184 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 10458749452596171553) ^ 1494107064656595936 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 10458749452596171553) ^ 171454909058953632 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 10458749452596171553) ^ 9259816226976 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (13 : ZMod 10458749452596171553) ^ 138898563552 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_16465120399923294493 : Nat.Prime 16465120399923294493 := by
  apply lucas_primality 16465120399923294493 (2 : ZMod 16465120399923294493)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5298299, 1), (86322885053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5298299, 1), (86322885053, 1)] : List FactorBlock).map factorBlockValue).prod) = 16465120399923294493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5298299
      · exact prime_seventyThreeBS_86322885053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16465120399923294493) ^ 8232560199961647246 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16465120399923294493) ^ 5488373466641098164 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16465120399923294493) ^ 3107623861908 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16465120399923294493) ^ 190738764 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_29179334107410661597 : Nat.Prime 29179334107410661597 := by
  apply lucas_primality 29179334107410661597 (2 : ZMod 29179334107410661597)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1031, 1), (106859, 1), (22071119377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1031, 1), (106859, 1), (22071119377, 1)] : List FactorBlock).map factorBlockValue).prod) = 29179334107410661597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1031
      · exact prime_seventyThreeBS_106859
      · exact prime_seventyThreeBS_22071119377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29179334107410661597) ^ 14589667053705330798 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29179334107410661597) ^ 9726444702470220532 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29179334107410661597) ^ 28301972946082116 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29179334107410661597) ^ 273063888932244 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29179334107410661597) ^ 1322059548 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_45764404222215137383 : Nat.Prime 45764404222215137383 := by
  apply lucas_primality 45764404222215137383 (5 : ZMod 45764404222215137383)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (311, 1), (39521, 1), (2686434577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (311, 1), (39521, 1), (2686434577, 1)] : List FactorBlock).map factorBlockValue).prod) = 45764404222215137383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_311
      · exact prime_seventyThreeBS_39521
      · exact prime_seventyThreeBS_2686434577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 45764404222215137383) ^ 22882202111107568691 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 15254801407405045794 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 6537772031745019626 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 4160400383837739762 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 147152425151817162 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 1157976878677542 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45764404222215137383) ^ 17035368966 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_72154643092931450921 : Nat.Prime 72154643092931450921 := by
  apply lucas_primality 72154643092931450921 (3 : ZMod 72154643092931450921)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (53, 1), (97, 1), (139, 1), (145121, 1), (1581317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (53, 1), (97, 1), (139, 1), (145121, 1), (1581317, 1)] : List FactorBlock).map factorBlockValue).prod) = 72154643092931450921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_53
      · exact prime_seventyThreeBS_97
      · exact prime_seventyThreeBS_139
      · exact prime_seventyThreeBS_145121
      · exact prime_seventyThreeBS_1581317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72154643092931450921) ^ 36077321546465725460 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 14430928618586290184 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 6559513008448313720 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 1361408360243989640 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 743862299927128360 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 519098151747708280 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 497203320628520 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 72154643092931450921) ^ 45629461450760 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_74519471650778658787 : Nat.Prime 74519471650778658787 := by
  apply lucas_primality 74519471650778658787 (2 : ZMod 74519471650778658787)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3701, 1), (77951, 1), (106219, 1), (405299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3701, 1), (77951, 1), (106219, 1), (405299, 1)] : List FactorBlock).map factorBlockValue).prod) = 74519471650778658787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_3701
      · exact prime_seventyThreeBS_77951
      · exact prime_seventyThreeBS_106219
      · exact prime_seventyThreeBS_405299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74519471650778658787) ^ 37259735825389329393 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 74519471650778658787) ^ 24839823883592886262 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 74519471650778658787) ^ 20134955863490586 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 74519471650778658787) ^ 955978392205086 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 74519471650778658787) ^ 701564424921894 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 74519471650778658787) ^ 183862954635414 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_75825083224718192941 : Nat.Prime 75825083224718192941 := by
  apply lucas_primality 75825083224718192941 (2 : ZMod 75825083224718192941)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (189468193, 1), (6669992293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (189468193, 1), (6669992293, 1)] : List FactorBlock).map factorBlockValue).prod) = 75825083224718192941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_189468193
      · exact prime_seventyThreeBS_6669992293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75825083224718192941) ^ 37912541612359096470 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825083224718192941) ^ 25275027741572730980 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825083224718192941) ^ 15165016644943638588 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825083224718192941) ^ 400199537580 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825083224718192941) ^ 11368091580 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_124233085639053615751 : Nat.Prime 124233085639053615751 := by
  apply lucas_primality 124233085639053615751 (3 : ZMod 124233085639053615751)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (165644114185404821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (165644114185404821, 1)] : List FactorBlock).map factorBlockValue).prod) = 124233085639053615751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_165644114185404821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 124233085639053615751) ^ 62116542819526807875 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 124233085639053615751) ^ 41411028546351205250 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 124233085639053615751) ^ 24846617127810723150 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 124233085639053615751) ^ 750 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_125278351087892118253 : Nat.Prime 125278351087892118253 := by
  apply lucas_primality 125278351087892118253 (5 : ZMod 125278351087892118253)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (614109564156333913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (614109564156333913, 1)] : List FactorBlock).map factorBlockValue).prod) = 125278351087892118253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_614109564156333913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 125278351087892118253) ^ 62639175543946059126 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 125278351087892118253) ^ 41759450362630706084 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 125278351087892118253) ^ 7369314769876006956 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 125278351087892118253) ^ 204 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_140131747200374013899 : Nat.Prime 140131747200374013899 := by
  apply lucas_primality 140131747200374013899 (2 : ZMod 140131747200374013899)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (6369624872744273359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (6369624872744273359, 1)] : List FactorBlock).map factorBlockValue).prod) = 140131747200374013899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_6369624872744273359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140131747200374013899) ^ 70065873600187006949 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 140131747200374013899) ^ 12739249745488546718 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 140131747200374013899) ^ 22 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_150287210809583511233 : Nat.Prime 150287210809583511233 := by
  apply lucas_primality 150287210809583511233 (3 : ZMod 150287210809583511233)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (1399, 1), (1933, 1), (45702386731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (1399, 1), (1933, 1), (45702386731, 1)] : List FactorBlock).map factorBlockValue).prod) = 150287210809583511233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_1399
      · exact prime_seventyThreeBS_1933
      · exact prime_seventyThreeBS_45702386731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150287210809583511233) ^ 75143605404791755616 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150287210809583511233) ^ 7909853200504395328 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150287210809583511233) ^ 107424739678043968 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150287210809583511233) ^ 77748169068589504 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150287210809583511233) ^ 3288388672 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_215767604729963535437 : Nat.Prime 215767604729963535437 := by
  apply lucas_primality 215767604729963535437 (3 : ZMod 215767604729963535437)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (911, 1), (542281, 1), (9926377759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (911, 1), (542281, 1), (9926377759, 1)] : List FactorBlock).map factorBlockValue).prod) = 215767604729963535437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_911
      · exact prime_seventyThreeBS_542281
      · exact prime_seventyThreeBS_9926377759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 215767604729963535437) ^ 107883802364981767718 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 215767604729963535437) ^ 19615236793633048676 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 215767604729963535437) ^ 236846986531244276 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 215767604729963535437) ^ 397888926091756 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 215767604729963535437) ^ 21736791604 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_335437910721879416287 : Nat.Prime 335437910721879416287 := by
  apply lucas_primality 335437910721879416287 (5 : ZMod 335437910721879416287)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1779222311, 1), (2856524761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1779222311, 1), (2856524761, 1)] : List FactorBlock).map factorBlockValue).prod) = 335437910721879416287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_1779222311
      · exact prime_seventyThreeBS_2856524761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 335437910721879416287) ^ 167718955360939708143 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 335437910721879416287) ^ 111812636907293138762 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 335437910721879416287) ^ 30494355520170856026 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 335437910721879416287) ^ 188530634226 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 335437910721879416287) ^ 117428672526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_514072523612528701001 : Nat.Prime 514072523612528701001 := by
  apply lucas_primality 514072523612528701001 (3 : ZMod 514072523612528701001)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (1931, 1), (126031, 1), (2112344441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (1931, 1), (126031, 1), (2112344441, 1)] : List FactorBlock).map factorBlockValue).prod) = 514072523612528701001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_1931
      · exact prime_seventyThreeBS_126031
      · exact prime_seventyThreeBS_2112344441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 514072523612528701001) ^ 257036261806264350500 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 514072523612528701001) ^ 102814504722505740200 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 514072523612528701001) ^ 266220882243671000 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 514072523612528701001) ^ 4078937115571000 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 514072523612528701001) ^ 243365861000 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_833499765543645825397 : Nat.Prime 833499765543645825397 := by
  apply lucas_primality 833499765543645825397 (15 : ZMod 833499765543645825397)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (115279, 1), (35442562517281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (115279, 1), (35442562517281, 1)] : List FactorBlock).map factorBlockValue).prod) = 833499765543645825397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_115279
      · exact prime_seventyThreeBS_35442562517281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 833499765543645825397) ^ 416749882771822912698 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 833499765543645825397) ^ 277833255181215275132 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 833499765543645825397) ^ 49029397973155636788 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 833499765543645825397) ^ 7230282753525324 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 833499765543645825397) ^ 23516916 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1392501899434351493497 : Nat.Prime 1392501899434351493497 := by
  apply lucas_primality 1392501899434351493497 (10 : ZMod 1392501899434351493497)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (7366349, 1), (271602814349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (7366349, 1), (271602814349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1392501899434351493497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_7366349
      · exact prime_seventyThreeBS_271602814349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1392501899434351493497) ^ 696250949717175746748 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1392501899434351493497) ^ 464167299811450497832 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1392501899434351493497) ^ 48017306877046603224 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1392501899434351493497) ^ 189035558786904 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1392501899434351493497) ^ 5126978904 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2116275724223143953523 : Nat.Prime 2116275724223143953523 := by
  apply lucas_primality 2116275724223143953523 (3 : ZMod 2116275724223143953523)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (47, 1), (3319, 1), (13379170393811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (47, 1), (3319, 1), (13379170393811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2116275724223143953523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_3319
      · exact prime_seventyThreeBS_13379170393811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2116275724223143953523) ^ 1058137862111571976761 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2116275724223143953523) ^ 705425241407714651174 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2116275724223143953523) ^ 162790440324857227194 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2116275724223143953523) ^ 45027143068577530926 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2116275724223143953523) ^ 637624502628244638 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2116275724223143953523) ^ 158176902 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2604450071790018695273 : Nat.Prime 2604450071790018695273 := by
  apply lucas_primality 2604450071790018695273 (3 : ZMod 2604450071790018695273)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (401, 1), (811860994947013309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (401, 1), (811860994947013309, 1)] : List FactorBlock).map factorBlockValue).prod) = 2604450071790018695273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_401
      · exact prime_seventyThreeBS_811860994947013309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2604450071790018695273) ^ 1302225035895009347636 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604450071790018695273) ^ 6494887959576106472 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604450071790018695273) ^ 3208 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3539454248344816857113 : Nat.Prime 3539454248344816857113 := by
  apply lucas_primality 3539454248344816857113 (3 : ZMod 3539454248344816857113)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1069609, 1), (1172539, 1), (352771889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1069609, 1), (1172539, 1), (352771889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3539454248344816857113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_1069609
      · exact prime_seventyThreeBS_1172539
      · exact prime_seventyThreeBS_352771889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3539454248344816857113) ^ 1769727124172408428556 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3539454248344816857113) ^ 3309110383649368 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3539454248344816857113) ^ 3018623899371208 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3539454248344816857113) ^ 10033266138008 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_6804918037840670224369 : Nat.Prime 6804918037840670224369 := by
  apply lucas_primality 6804918037840670224369 (11 : ZMod 6804918037840670224369)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1249, 1), (113506105515089909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1249, 1), (113506105515089909, 1)] : List FactorBlock).map factorBlockValue).prod) = 6804918037840670224369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_1249
      · exact prime_seventyThreeBS_113506105515089909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6804918037840670224369) ^ 3402459018920335112184 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6804918037840670224369) ^ 2268306012613556741456 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6804918037840670224369) ^ 5448293064724315632 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6804918037840670224369) ^ 59952 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_9308786433495052605683 : Nat.Prime 9308786433495052605683 := by
  apply lucas_primality 9308786433495052605683 (2 : ZMod 9308786433495052605683)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1321, 1), (36877, 1), (13649182166339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1321, 1), (36877, 1), (13649182166339, 1)] : List FactorBlock).map factorBlockValue).prod) = 9308786433495052605683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_1321
      · exact prime_seventyThreeBS_36877
      · exact prime_seventyThreeBS_13649182166339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9308786433495052605683) ^ 4654393216747526302841 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308786433495052605683) ^ 1329826633356436086526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308786433495052605683) ^ 7046772470473166242 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308786433495052605683) ^ 252427974984273466 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308786433495052605683) ^ 682003238 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_12498898637403341458549 : Nat.Prime 12498898637403341458549 := by
  apply lucas_primality 12498898637403341458549 (6 : ZMod 12498898637403341458549)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (557, 1), (997, 1), (201911, 1), (844476331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (557, 1), (997, 1), (201911, 1), (844476331, 1)] : List FactorBlock).map factorBlockValue).prod) = 12498898637403341458549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_557
      · exact prime_seventyThreeBS_997
      · exact prime_seventyThreeBS_201911
      · exact prime_seventyThreeBS_844476331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12498898637403341458549) ^ 6249449318701670729274 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 4166299545801113819516 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 1136263512491212859868 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 22439674393901869764 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 12536508161889008484 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 61903009927162668 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 12498898637403341458549) ^ 14800768450908 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_13620818380766863447633 : Nat.Prime 13620818380766863447633 := by
  apply lucas_primality 13620818380766863447633 (5 : ZMod 13620818380766863447633)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (29, 1), (291061231, 1), (3056236231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (29, 1), (291061231, 1), (3056236231, 1)] : List FactorBlock).map factorBlockValue).prod) = 13620818380766863447633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_11
      · exact prime_seventyThreeBS_29
      · exact prime_seventyThreeBS_291061231
      · exact prime_seventyThreeBS_3056236231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13620818380766863447633) ^ 6810409190383431723816 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13620818380766863447633) ^ 4540272793588954482544 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13620818380766863447633) ^ 1238256216433351222512 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13620818380766863447633) ^ 469683392440236670608 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13620818380766863447633) ^ 46797089169072 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13620818380766863447633) ^ 4456729569072 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_15330861344188841250281 : Nat.Prime 15330861344188841250281 := by
  apply lucas_primality 15330861344188841250281 (3 : ZMod 15330861344188841250281)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (3083, 1), (13559701, 1), (705244283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (3083, 1), (13559701, 1), (705244283, 1)] : List FactorBlock).map factorBlockValue).prod) = 15330861344188841250281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_3083
      · exact prime_seventyThreeBS_13559701
      · exact prime_seventyThreeBS_705244283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15330861344188841250281) ^ 7665430672094420625140 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 15330861344188841250281) ^ 3066172268837768250056 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 15330861344188841250281) ^ 1179297026476064711560 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 15330861344188841250281) ^ 4972708836908479160 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 15330861344188841250281) ^ 1130619424734280 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 15330861344188841250281) ^ 21738370255160 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_20264002884092578006367 : Nat.Prime 20264002884092578006367 := by
  apply lucas_primality 20264002884092578006367 (5 : ZMod 20264002884092578006367)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1546706167, 1), (123598032133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1546706167, 1), (123598032133, 1)] : List FactorBlock).map factorBlockValue).prod) = 20264002884092578006367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_53
      · exact prime_seventyThreeBS_1546706167
      · exact prime_seventyThreeBS_123598032133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20264002884092578006367) ^ 10132001442046289003183 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20264002884092578006367) ^ 382339677058350528422 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20264002884092578006367) ^ 13101391406098 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 20264002884092578006367) ^ 163950853702 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_48653506742003986024043 : Nat.Prime 48653506742003986024043 := by
  apply lucas_primality 48653506742003986024043 (2 : ZMod 48653506742003986024043)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2687, 1), (30763, 1), (42839, 1), (6869869319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2687, 1), (30763, 1), (42839, 1), (6869869319, 1)] : List FactorBlock).map factorBlockValue).prod) = 48653506742003986024043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_2687
      · exact prime_seventyThreeBS_30763
      · exact prime_seventyThreeBS_42839
      · exact prime_seventyThreeBS_6869869319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48653506742003986024043) ^ 24326753371001993012021 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48653506742003986024043) ^ 18106999159659094166 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48653506742003986024043) ^ 1581559234860188734 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48653506742003986024043) ^ 1135729282709773478 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 48653506742003986024043) ^ 7082158987718 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_66213316500649839524099 : Nat.Prime 66213316500649839524099 := by
  apply lucas_primality 66213316500649839524099 (2 : ZMod 66213316500649839524099)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (792293, 1), (1691527, 1), (24703050859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (792293, 1), (1691527, 1), (24703050859, 1)] : List FactorBlock).map factorBlockValue).prod) = 66213316500649839524099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_792293
      · exact prime_seventyThreeBS_1691527
      · exact prime_seventyThreeBS_24703050859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66213316500649839524099) ^ 33106658250324919762049 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66213316500649839524099) ^ 83571755020743386 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66213316500649839524099) ^ 39144108548459374 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66213316500649839524099) ^ 2680370002822 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_120483021823081336548331 : Nat.Prime 120483021823081336548331 := by
  apply lucas_primality 120483021823081336548331 (11 : ZMod 120483021823081336548331)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (2111, 1), (4723, 1), (41579, 1), (509883287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (2111, 1), (4723, 1), (41579, 1), (509883287, 1)] : List FactorBlock).map factorBlockValue).prod) = 120483021823081336548331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_2111
      · exact prime_seventyThreeBS_4723
      · exact prime_seventyThreeBS_41579
      · exact prime_seventyThreeBS_509883287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 120483021823081336548331) ^ 60241510911540668274165 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 40161007274360445516110 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 24096604364616267309666 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 6341211674899017713070 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 57073908964036635030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 25509850057819465710 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 2897689261961118270 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 120483021823081336548331) ^ 236295295207590 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_132426633001299679048199 : Nat.Prime 132426633001299679048199 := by
  apply lucas_primality 132426633001299679048199 (7 : ZMod 132426633001299679048199)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (66213316500649839524099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (66213316500649839524099, 1)] : List FactorBlock).map factorBlockValue).prod) = 132426633001299679048199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_66213316500649839524099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 132426633001299679048199) ^ 66213316500649839524099 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 132426633001299679048199) ^ 2 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_502252032679260175214473 : Nat.Prime 502252032679260175214473 := by
  apply lucas_primality 502252032679260175214473 (5 : ZMod 502252032679260175214473)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (41, 1), (16465120399923294493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (41, 1), (16465120399923294493, 1)] : List FactorBlock).map factorBlockValue).prod) = 502252032679260175214473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_16465120399923294493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 502252032679260175214473) ^ 251126016339630087607236 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 502252032679260175214473) ^ 167417344226420058404824 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 502252032679260175214473) ^ 16201678473524521781112 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 502252032679260175214473) ^ 12250049577542931102792 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 502252032679260175214473) ^ 30504 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_692615903790334735557343 : Nat.Prime 692615903790334735557343 := by
  apply lucas_primality 692615903790334735557343 (3 : ZMod 692615903790334735557343)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (31, 1), (109, 1), (3089, 1), (569617, 1), (26633279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (31, 1), (109, 1), (3089, 1), (569617, 1), (26633279, 1)] : List FactorBlock).map factorBlockValue).prod) = 692615903790334735557343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_31
      · exact prime_seventyThreeBS_109
      · exact prime_seventyThreeBS_3089
      · exact prime_seventyThreeBS_569617
      · exact prime_seventyThreeBS_26633279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 692615903790334735557343) ^ 346307951895167367778671 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 230871967930111578519114 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 22342448509365636630882 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 6354274346700318674838 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 224220104820438567678 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 1215932642091676926 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 692615903790334735557343) ^ 26005656449224098 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1313909852015742026129303 : Nat.Prime 1313909852015742026129303 := by
  apply lucas_primality 1313909852015742026129303 (7 : ZMod 1313909852015742026129303)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (47, 1), (59, 1), (8081, 1), (14221, 1), (50281312307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (47, 1), (59, 1), (8081, 1), (14221, 1), (50281312307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1313909852015742026129303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_41
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_8081
      · exact prime_seventyThreeBS_14221
      · exact prime_seventyThreeBS_50281312307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1313909852015742026129303) ^ 656954926007871013064651 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 32046581756481512832422 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 27955528766292383534666 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 22269658508741390273378 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 162592482615485957942 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 92392226426815415662 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1313909852015742026129303) ^ 26131176608786 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1740626475596596227100607 : Nat.Prime 1740626475596596227100607 := by
  apply lucas_primality 1740626475596596227100607 (5 : ZMod 1740626475596596227100607)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5791, 1), (150287210809583511233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5791, 1), (150287210809583511233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1740626475596596227100607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5791
      · exact prime_seventyThreeBS_150287210809583511233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1740626475596596227100607) ^ 870313237798298113550303 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1740626475596596227100607) ^ 300574421619167022466 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1740626475596596227100607) ^ 11582 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_1799568017254447147111687 : Nat.Prime 1799568017254447147111687 := by
  apply lucas_primality 1799568017254447147111687 (6 : ZMod 1799568017254447147111687)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (564409, 1), (1885349, 1), (720866051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (564409, 1), (1885349, 1), (720866051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1799568017254447147111687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_17
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_564409
      · exact prime_seventyThreeBS_1885349
      · exact prime_seventyThreeBS_720866051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1799568017254447147111687) ^ 899784008627223573555843 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 599856005751482382370562 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 105856942191438067477158 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 78242087706715093352682 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 3188411271355430454 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 954501271252403214 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1799568017254447147111687) ^ 2496397236016386 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2811253502915505886916267 : Nat.Prime 2811253502915505886916267 := by
  apply lucas_primality 2811253502915505886916267 (2 : ZMod 2811253502915505886916267)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (9308786433495052605683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (9308786433495052605683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2811253502915505886916267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_151
      · exact prime_seventyThreeBS_9308786433495052605683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2811253502915505886916267) ^ 1405626751457752943458133 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2811253502915505886916267) ^ 18617572866990105211366 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2811253502915505886916267) ^ 302 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_3397184906101398572262523 : Nat.Prime 3397184906101398572262523 := by
  apply lucas_primality 3397184906101398572262523 (2 : ZMod 3397184906101398572262523)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (59, 1), (72154643092931450921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (59, 1), (72154643092931450921, 1)] : List FactorBlock).map factorBlockValue).prod) = 3397184906101398572262523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_19
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_72154643092931450921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3397184906101398572262523) ^ 1698592453050699286131261 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3397184906101398572262523) ^ 1132394968700466190754174 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3397184906101398572262523) ^ 485312129443056938894646 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3397184906101398572262523) ^ 178799205584284135382238 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3397184906101398572262523) ^ 57579405188159297834958 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3397184906101398572262523) ^ 47082 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_28446104989949252052844231 : Nat.Prime 28446104989949252052844231 := by
  apply lucas_primality 28446104989949252052844231 (15 : ZMod 28446104989949252052844231)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (239, 1), (397, 1), (743, 1), (558829, 1), (24068298941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (239, 1), (397, 1), (743, 1), (558829, 1), (24068298941, 1)] : List FactorBlock).map factorBlockValue).prod) = 28446104989949252052844231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_239
      · exact prime_seventyThreeBS_397
      · exact prime_seventyThreeBS_743
      · exact prime_seventyThreeBS_558829
      · exact prime_seventyThreeBS_24068298941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 28446104989949252052844231) ^ 14223052494974626026422115 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 9482034996649750684281410 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 5689220997989850410568846 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 119021359790582644572570 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 71652657405413733130590 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 38285471049729814337610 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 50903057983657347870 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (15 : ZMod 28446104989949252052844231) ^ 1181890962036030 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_53873584606433227670617601 : Nat.Prime 53873584606433227670617601 := by
  apply lucas_primality 53873584606433227670617601 (3 : ZMod 53873584606433227670617601)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 2), (1185013, 1), (3551753269692059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 2), (1185013, 1), (3551753269692059, 1)] : List FactorBlock).map factorBlockValue).prod) = 53873584606433227670617601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_1185013
      · exact prime_seventyThreeBS_3551753269692059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53873584606433227670617601) ^ 26936792303216613835308800 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 53873584606433227670617601) ^ 10774716921286645534123520 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 53873584606433227670617601) ^ 45462441852058355200 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 53873584606433227670617601) ^ 15168166400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_70626417790103134802233549 : Nat.Prime 70626417790103134802233549 := by
  apply lucas_primality 70626417790103134802233549 (2 : ZMod 70626417790103134802233549)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 2), (647723, 1), (12489721, 1), (1375270747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 2), (647723, 1), (12489721, 1), (1375270747, 1)] : List FactorBlock).map factorBlockValue).prod) = 70626417790103134802233549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_23
      · exact prime_seventyThreeBS_647723
      · exact prime_seventyThreeBS_12489721
      · exact prime_seventyThreeBS_1375270747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70626417790103134802233549) ^ 35313208895051567401116774 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70626417790103134802233549) ^ 23542139263367711600744516 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70626417790103134802233549) ^ 3070713816961005860966676 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70626417790103134802233549) ^ 109037995856412594276 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70626417790103134802233549) ^ 5654763448287046188 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 70626417790103134802233549) ^ 51354555416936484 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_185603188257002216620063219 : Nat.Prime 185603188257002216620063219 := by
  apply lucas_primality 185603188257002216620063219 (17 : ZMod 185603188257002216620063219)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (79, 1), (107, 1), (317, 1), (701, 1), (782053, 1), (296586581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (79, 1), (107, 1), (317, 1), (701, 1), (782053, 1), (296586581, 1)] : List FactorBlock).map factorBlockValue).prod) = 185603188257002216620063219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_71
      · exact prime_seventyThreeBS_79
      · exact prime_seventyThreeBS_107
      · exact prime_seventyThreeBS_317
      · exact prime_seventyThreeBS_701
      · exact prime_seventyThreeBS_782053
      · exact prime_seventyThreeBS_296586581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 185603188257002216620063219) ^ 92801594128501108310031609 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 61867729419000738873354406 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 2614129412070453755212158 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 2349407446291167298988142 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 1734609236046749688037974 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 585499016583603207003354 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 264769170124111578630618 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 237328145607781335306 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (17 : ZMod 185603188257002216620063219) ^ 625797659594727978 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_190519829005532076662978801 : Nat.Prime 190519829005532076662978801 := by
  apply lucas_primality 190519829005532076662978801 (3 : ZMod 190519829005532076662978801)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (113, 1), (3529, 1), (67957, 1), (150617, 1), (16670317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (113, 1), (3529, 1), (67957, 1), (150617, 1), (16670317, 1)] : List FactorBlock).map factorBlockValue).prod) = 190519829005532076662978801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_113
      · exact prime_seventyThreeBS_3529
      · exact prime_seventyThreeBS_67957
      · exact prime_seventyThreeBS_150617
      · exact prime_seventyThreeBS_16670317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 190519829005532076662978801) ^ 95259914502766038331489400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 38103965801106415332595760 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 27217118429361725237568400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 1686016185889664395247600 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 53986916691848137337200 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 2803535014870169028400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 1264929118263755596400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 190519829005532076662978801) ^ 11428686629386356400 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_245186029941778496387299423 : Nat.Prime 245186029941778496387299423 := by
  apply lucas_primality 245186029941778496387299423 (5 : ZMod 245186029941778496387299423)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (692615903790334735557343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (692615903790334735557343, 1)] : List FactorBlock).map factorBlockValue).prod) = 245186029941778496387299423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_59
      · exact prime_seventyThreeBS_692615903790334735557343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 245186029941778496387299423) ^ 122593014970889248193649711 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 245186029941778496387299423) ^ 81728676647259498795766474 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 245186029941778496387299423) ^ 4155695422742008413344058 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (5 : ZMod 245186029941778496387299423) ^ 354 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2465870929700172306523697053 : Nat.Prime 2465870929700172306523697053 := by
  apply lucas_primality 2465870929700172306523697053 (2 : ZMod 2465870929700172306523697053)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (3102256515871, 1), (3154220823431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (3102256515871, 1), (3154220823431, 1)] : List FactorBlock).map factorBlockValue).prod) = 2465870929700172306523697053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_3102256515871
      · exact prime_seventyThreeBS_3154220823431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2465870929700172306523697053) ^ 1232935464850086153261848526 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465870929700172306523697053) ^ 821956976566724102174565684 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465870929700172306523697053) ^ 352267275671453186646242436 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465870929700172306523697053) ^ 794863647504612 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2465870929700172306523697053) ^ 781768641999492 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_2538396545279589139068511673 : Nat.Prime 2538396545279589139068511673 := by
  apply lucas_primality 2538396545279589139068511673 (3 : ZMod 2538396545279589139068511673)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (21419, 1), (2116275724223143953523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (21419, 1), (2116275724223143953523, 1)] : List FactorBlock).map factorBlockValue).prod) = 2538396545279589139068511673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7
      · exact prime_seventyThreeBS_21419
      · exact prime_seventyThreeBS_2116275724223143953523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2538396545279589139068511673) ^ 1269198272639794569534255836 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2538396545279589139068511673) ^ 362628077897084162724073096 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2538396545279589139068511673) ^ 118511440556496061397288 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2538396545279589139068511673) ^ 1199464 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_5394092658719126920520587301 : Nat.Prime 5394092658719126920520587301 := by
  apply lucas_primality 5394092658719126920520587301 (2 : ZMod 5394092658719126920520587301)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 2), (55717, 1), (5728540309018458901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 2), (55717, 1), (5728540309018458901, 1)] : List FactorBlock).map factorBlockValue).prod) = 5394092658719126920520587301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_55717
      · exact prime_seventyThreeBS_5728540309018458901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5394092658719126920520587301) ^ 2697046329359563460260293650 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5394092658719126920520587301) ^ 1078818531743825384104117460 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5394092658719126920520587301) ^ 414930204516855916963122100 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5394092658719126920520587301) ^ 96812331222411955426900 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5394092658719126920520587301) ^ 941617300 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_7192123544958835894027449739 : Nat.Prime 7192123544958835894027449739 := by
  apply lucas_primality 7192123544958835894027449739 (2 : ZMod 7192123544958835894027449739)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6981604429, 1), (171692233451964787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6981604429, 1), (171692233451964787, 1)] : List FactorBlock).map factorBlockValue).prod) = 7192123544958835894027449739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_3
      · exact prime_seventyThreeBS_6981604429
      · exact prime_seventyThreeBS_171692233451964787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7192123544958835894027449739) ^ 3596061772479417947013724869 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7192123544958835894027449739) ^ 2397374514986278631342483246 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7192123544958835894027449739) ^ 1030153400711788722 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7192123544958835894027449739) ^ 41889626574 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_28768494179835343576109798957 : Nat.Prime 28768494179835343576109798957 := by
  apply lucas_primality 28768494179835343576109798957 (2 : ZMod 28768494179835343576109798957)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7192123544958835894027449739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7192123544958835894027449739, 1)] : List FactorBlock).map factorBlockValue).prod) = 28768494179835343576109798957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_7192123544958835894027449739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28768494179835343576109798957) ^ 14384247089917671788054899478 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 28768494179835343576109798957) ^ 4 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_43152741269753015364164698421 : Nat.Prime 43152741269753015364164698421 := by
  apply lucas_primality 43152741269753015364164698421 (2 : ZMod 43152741269753015364164698421)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (727, 1), (48653506742003986024043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (727, 1), (48653506742003986024043, 1)] : List FactorBlock).map factorBlockValue).prod) = 43152741269753015364164698421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_61
      · exact prime_seventyThreeBS_727
      · exact prime_seventyThreeBS_48653506742003986024043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43152741269753015364164698421) ^ 21576370634876507682082349210 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698421) ^ 8630548253950603072832939684 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698421) ^ 707421988028737956789585220 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698421) ^ 59357278225244862949332460 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698421) ^ 886940 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_43152741269753015364164698451 : Nat.Prime 43152741269753015364164698451 := by
  apply lucas_primality 43152741269753015364164698451 (2 : ZMod 43152741269753015364164698451)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (307, 1), (2811253502915505886916267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (307, 1), (2811253502915505886916267, 1)] : List FactorBlock).map factorBlockValue).prod) = 43152741269753015364164698451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_5
      · exact prime_seventyThreeBS_307
      · exact prime_seventyThreeBS_2811253502915505886916267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43152741269753015364164698451) ^ 21576370634876507682082349225 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698451) ^ 8630548253950603072832939690 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698451) ^ 140562675145775294345813350 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43152741269753015364164698451) ^ 15350 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_86305482539506030728329396843 : Nat.Prime 86305482539506030728329396843 := by
  apply lucas_primality 86305482539506030728329396843 (2 : ZMod 86305482539506030728329396843)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43152741269753015364164698421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43152741269753015364164698421, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_43152741269753015364164698421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 86305482539506030728329396843) ^ 43152741269753015364164698421 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (2 : ZMod 86305482539506030728329396843) ^ 2 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem prime_seventyThreeBS_86305482539506030728329396879 : Nat.Prime 86305482539506030728329396879 := by
  apply lucas_primality 86305482539506030728329396879 (11 : ZMod 86305482539506030728329396879)
  · rw [← seventyThreeBSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (70626417790103134802233549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (70626417790103134802233549, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyThreeBS_2
      · exact prime_seventyThreeBS_13
      · exact prime_seventyThreeBS_47
      · exact prime_seventyThreeBS_70626417790103134802233549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86305482539506030728329396879) ^ 43152741269753015364164698439 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 86305482539506030728329396879) ^ 6638883272269694671409953606 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 86305482539506030728329396879) ^ 1836286862542681504858072274 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide
    · change (11 : ZMod 86305482539506030728329396879) ^ 1222 ≠ 1
      rw [← seventyThreeBSFastPow_eq_pow]
      decide

private theorem phi_seventyThreeBS_86305482539506030728329396800 : Nat.totient 86305482539506030728329396800 = 31866067769430082014268416000 := by
  rw [← show ((([(2, 6), (5, 2), (13, 2), (55717, 1), (5728540309018458901, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_13, prime_seventyThreeBS_55717, prime_seventyThreeBS_5728540309018458901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396801 : Nat.totient 86305482539506030728329396801 = 85853580378532828209056993680 := by
  rw [← show ((([(191, 1), (2094203, 1), (215767604729963535437, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_191, prime_seventyThreeBS_2094203, prime_seventyThreeBS_215767604729963535437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396802 : Nat.totient 86305482539506030728329396802 = 28445252672196744210086092800 := by
  rw [← show ((([(2, 1), (3, 2), (89, 1), (53873584606433227670617601, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_89, prime_seventyThreeBS_53873584606433227670617601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396803 : Nat.totient 86305482539506030728329396803 = 85864933859233475151933050400 := by
  rw [← show ((([(197, 1), (35051, 1), (12498898637403341458549, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_197, prime_seventyThreeBS_35051, prime_seventyThreeBS_12498898637403341458549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396804 : Nat.totient 86305482539506030728329396804 = 41510565180357087895808666400 := by
  rw [← show ((([(2, 2), (31, 1), (167, 1), (471703, 1), (8835509342226014671, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_31, prime_seventyThreeBS_167, prime_seventyThreeBS_471703, prime_seventyThreeBS_8835509342226014671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396805 : Nat.totient 86305482539506030728329396805 = 45999120529692863164772075520 := by
  rw [← show ((([(3, 1), (5, 1), (1559, 1), (48673, 1), (75825083224718192941, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_1559, prime_seventyThreeBS_48673, prime_seventyThreeBS_75825083224718192941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396806 : Nat.totient 86305482539506030728329396806 = 35377863578522430601336134720 := by
  rw [← show ((([(2, 1), (7, 1), (23, 1), (17483, 1), (15330861344188841250281, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_7, prime_seventyThreeBS_23, prime_seventyThreeBS_17483, prime_seventyThreeBS_15330861344188841250281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396807 : Nat.totient 86305482539506030728329396807 = 86305479000051782383488155856 := by
  rw [← show ((([(24383839, 1), (3539454248344816857113, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_24383839, prime_seventyThreeBS_3539454248344816857113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396808 : Nat.totient 86305482539506030728329396808 = 26082885339184436939273011200 := by
  rw [← show ((([(2, 3), (3, 1), (11, 1), (1097, 1), (1489, 1), (1607, 1), (2081, 1), (229753, 1), (260485759, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_11, prime_seventyThreeBS_1097, prime_seventyThreeBS_1489, prime_seventyThreeBS_1607, prime_seventyThreeBS_2081, prime_seventyThreeBS_229753, prime_seventyThreeBS_260485759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396809 : Nat.totient 86305482539506030728329396809 = 86304315598956645402923867520 := by
  rw [← show ((([(80471, 1), (951449, 1), (23161363, 1), (48668656717, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_80471, prime_seventyThreeBS_951449, prime_seventyThreeBS_23161363, prime_seventyThreeBS_48668656717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396810 : Nat.totient 86305482539506030728329396810 = 34521278498190339896140128000 := by
  rw [← show ((([(2, 1), (5, 1), (42701, 1), (326149, 1), (173318491, 1), (3575521459, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_42701, prime_seventyThreeBS_326149, prime_seventyThreeBS_173318491, prime_seventyThreeBS_3575521459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396811 : Nat.totient 86305482539506030728329396811 = 57536979106365262126591056000 := by
  rw [← show ((([(3, 3), (6217993, 1), (514072523612528701001, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_6217993, prime_seventyThreeBS_514072523612528701001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396812 : Nat.totient 86305482539506030728329396812 = 41664715701186112431930503680 := by
  rw [← show ((([(2, 2), (29, 2), (5525144411, 1), (4643428517462753, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_29, prime_seventyThreeBS_5525144411, prime_seventyThreeBS_4643428517462753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396813 : Nat.totient 86305482539506030728329396813 = 62653143942296655064126894080 := by
  rw [← show ((([(7, 1), (13, 1), (19, 1), (41, 1), (137, 1), (1344855647, 1), (6607897489603, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_7, prime_seventyThreeBS_13, prime_seventyThreeBS_19, prime_seventyThreeBS_41, prime_seventyThreeBS_137, prime_seventyThreeBS_1344855647, prime_seventyThreeBS_6607897489603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396814 : Nat.totient 86305482539506030728329396814 = 26570479896721550156868108288 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (83, 1), (149, 1), (1955451859, 1), (34988612772769, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_17, prime_seventyThreeBS_83, prime_seventyThreeBS_149, prime_seventyThreeBS_1955451859, prime_seventyThreeBS_34988612772769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396815 : Nat.totient 86305482539506030728329396815 = 69030797291980418988374447040 := by
  rw [← show ((([(5, 1), (5081, 1), (3397184906101398572262523, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_5081, prime_seventyThreeBS_3397184906101398572262523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396816 : Nat.totient 86305482539506030728329396816 = 43152741269753015364164698400 := by
  rw [← show ((([(2, 4), (5394092658719126920520587301, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5394092658719126920520587301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396817 : Nat.totient 86305482539506030728329396817 = 55946973281615049079635980544 := by
  rw [← show ((([(3, 1), (37, 1), (1613, 1), (219727, 1), (2193802932572944597, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_37, prime_seventyThreeBS_1613, prime_seventyThreeBS_219727, prime_seventyThreeBS_2193802932572944597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396818 : Nat.totient 86305482539506030728329396818 = 43152721005750131271584562516 := by
  rw [← show ((([(2, 1), (2129527, 1), (20264002884092578006367, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_2129527, prime_seventyThreeBS_20264002884092578006367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396819 : Nat.totient 86305482539506030728329396819 = 78420419610728608082723880960 := by
  rw [← show ((([(11, 1), (2017, 1), (371929, 1), (10458749452596171553, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_11, prime_seventyThreeBS_2017, prime_seventyThreeBS_371929, prime_seventyThreeBS_10458749452596171553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396820 : Nat.totient 86305482539506030728329396820 = 19726967437588765393873545600 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (7, 2), (3102256515871, 1), (3154220823431, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_7, prime_seventyThreeBS_3102256515871, prime_seventyThreeBS_3154220823431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396821 : Nat.totient 86305482539506030728329396821 = 86302908819412047061479595008 := by
  rw [← show ((([(33623, 1), (19415699, 1), (36063697, 1), (3665883409, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_33623, prime_seventyThreeBS_19415699, prime_seventyThreeBS_36063697, prime_seventyThreeBS_3665883409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396822 : Nat.totient 86305482539506030728329396822 = 43052605165214850237302644000 := by
  rw [← show ((([(2, 1), (431, 1), (3142487, 1), (1301881901, 1), (24472934063, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_431, prime_seventyThreeBS_3142487, prime_seventyThreeBS_1301881901, prime_seventyThreeBS_24472934063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396823 : Nat.totient 86305482539506030728329396823 = 57193966088400043851346944000 := by
  rw [← show ((([(3, 1), (251, 1), (523, 1), (23297, 1), (32479, 1), (289627016865259, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_251, prime_seventyThreeBS_523, prime_seventyThreeBS_23297, prime_seventyThreeBS_32479, prime_seventyThreeBS_289627016865259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396824 : Nat.totient 86305482539506030728329396824 = 42868737089223862617446091264 := by
  rw [← show ((([(2, 3), (157, 1), (4703, 1), (1487389, 1), (9823114393552237, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_157, prime_seventyThreeBS_4703, prime_seventyThreeBS_1487389, prime_seventyThreeBS_9823114393552237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396825 : Nat.totient 86305482539506030728329396825 = 68958252284889660385943764800 := by
  rw [← show ((([(5, 2), (859, 1), (11981, 1), (335437910721879416287, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_859, prime_seventyThreeBS_11981, prime_seventyThreeBS_335437910721879416287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396826 : Nat.totient 86305482539506030728329396826 = 26543819135178352236519899136 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (2267, 1), (156762043729, 1), (3113517746369, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_13, prime_seventyThreeBS_2267, prime_seventyThreeBS_156762043729, prime_seventyThreeBS_3113517746369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396827 : Nat.totient 86305482539506030728329396827 = 73814219647842270893472228672 := by
  rw [← show ((([(7, 1), (479, 1), (9883, 1), (2604450071790018695273, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_7, prime_seventyThreeBS_479, prime_seventyThreeBS_9883, prime_seventyThreeBS_2604450071790018695273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396828 : Nat.totient 86305482539506030728329396828 = 43013968383486277078806542400 := by
  rw [← show ((([(2, 2), (311, 1), (2377621, 1), (29179334107410661597, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_311, prime_seventyThreeBS_2377621, prime_seventyThreeBS_29179334107410661597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396829 : Nat.totient 86305482539506030728329396829 = 55035380159022900002448334560 := by
  rw [← show ((([(3, 2), (23, 1), (4959533237, 1), (84067326164485031, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_23, prime_seventyThreeBS_4959533237, prime_seventyThreeBS_84067326164485031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396830 : Nat.totient 86305482539506030728329396830 = 31383811628004003421134623520 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (153433327, 1), (5113591102757559239, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_11, prime_seventyThreeBS_153433327, prime_seventyThreeBS_5113591102757559239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396831 : Nat.totient 86305482539506030728329396831 = 79316697329801540616792711168 := by
  rw [← show ((([(17, 1), (47, 1), (433, 1), (1057853, 1), (1827107, 1), (129066759383, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_17, prime_seventyThreeBS_47, prime_seventyThreeBS_433, prime_seventyThreeBS_1057853, prime_seventyThreeBS_1827107, prime_seventyThreeBS_129066759383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396832 : Nat.totient 86305482539506030728329396832 = 27250011253053537293531418624 := by
  rw [← show ((([(2, 5), (3, 1), (19, 1), (6263, 1), (3630597013, 1), (2080909023097, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_19, prime_seventyThreeBS_6263, prime_seventyThreeBS_3630597013, prime_seventyThreeBS_2080909023097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396833 : Nat.totient 86305482539506030728329396833 = 85515472179931328430747318720 := by
  rw [← show ((([(199, 1), (241, 1), (1799568017254447147111687, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_199, prime_seventyThreeBS_241, prime_seventyThreeBS_1799568017254447147111687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396834 : Nat.totient 86305482539506030728329396834 = 36985743971275703114459632320 := by
  rw [← show ((([(2, 1), (7, 1), (27431, 1), (38069, 1), (5903332434799200829, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_7, prime_seventyThreeBS_27431, prime_seventyThreeBS_38069, prime_seventyThreeBS_5903332434799200829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396835 : Nat.totient 86305482539506030728329396835 = 44544765181680531988815172320 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (185603188257002216620063219, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_31, prime_seventyThreeBS_185603188257002216620063219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396836 : Nat.totient 86305482539506030728329396836 = 43083193371100819759397921280 := by
  rw [← show ((([(2, 2), (1061, 1), (1493, 1), (13620818380766863447633, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_1061, prime_seventyThreeBS_1493, prime_seventyThreeBS_13620818380766863447633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396837 : Nat.totient 86305482539506030728329396837 = 83367980484038715827927912256 := by
  rw [← show ((([(43, 1), (163, 1), (373, 1), (443, 1), (74519471650778658787, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_43, prime_seventyThreeBS_163, prime_seventyThreeBS_373, prime_seventyThreeBS_443, prime_seventyThreeBS_74519471650778658787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396838 : Nat.totient 86305482539506030728329396838 = 28430134962667416136970236800 := by
  rw [← show ((([(2, 1), (3, 5), (101, 1), (643, 1), (3083, 1), (886944090313260557, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_101, prime_seventyThreeBS_643, prime_seventyThreeBS_3083, prime_seventyThreeBS_886944090313260557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396839 : Nat.totient 86305482539506030728329396839 = 78316305256047533343436099584 := by
  rw [← show ((([(13, 1), (59, 1), (6225889, 1), (926566397, 1), (19505859949, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_13, prime_seventyThreeBS_59, prime_seventyThreeBS_6225889, prime_seventyThreeBS_926566397, prime_seventyThreeBS_19505859949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396840 : Nat.totient 86305482539506030728329396840 = 33909548058907098099316312320 := by
  rw [← show ((([(2, 3), (5, 1), (61, 1), (727, 1), (48653506742003986024043, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_61, prime_seventyThreeBS_727, prime_seventyThreeBS_48653506742003986024043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396841 : Nat.totient 86305482539506030728329396841 = 43149613754563229015359488000 := by
  rw [← show ((([(3, 1), (7, 1), (11, 2), (29, 1), (337, 1), (4337, 1), (801339220242766801, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_7, prime_seventyThreeBS_11, prime_seventyThreeBS_29, prime_seventyThreeBS_337, prime_seventyThreeBS_4337, prime_seventyThreeBS_801339220242766801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396842 : Nat.totient 86305482539506030728329396842 = 43152741269753015364164698420 := by
  rw [← show ((([(2, 1), (43152741269753015364164698421, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_43152741269753015364164698421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396843 : Nat.totient 86305482539506030728329396843 = 86305482539506030728329396842 := by
  rw [← show ((([(86305482539506030728329396843, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_86305482539506030728329396843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396844 : Nat.totient 86305482539506030728329396844 = 27723556351121809104022487040 := by
  rw [← show ((([(2, 2), (3, 1), (53, 1), (79, 1), (193, 1), (61231, 1), (327064883, 1), (444417959, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_53, prime_seventyThreeBS_79, prime_seventyThreeBS_193, prime_seventyThreeBS_61231, prime_seventyThreeBS_327064883, prime_seventyThreeBS_444417959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396845 : Nat.totient 86305482539506030728329396845 = 69040309462408111296531363840 := by
  rw [← show ((([(5, 1), (16937, 1), (2506881961, 1), (406535062245817, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_16937, prime_seventyThreeBS_2506881961, prime_seventyThreeBS_406535062245817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396846 : Nat.totient 86305482539506030728329396846 = 42692938535061691935332823360 := by
  rw [← show ((([(2, 1), (211, 1), (227, 1), (647, 1), (1392501899434351493497, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_211, prime_seventyThreeBS_227, prime_seventyThreeBS_647, prime_seventyThreeBS_1392501899434351493497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396847 : Nat.totient 86305482539506030728329396847 = 57536988359668163452952731248 := by
  rw [← show ((([(3, 2), (24189838675307, 1), (396426705802469, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_24189838675307, prime_seventyThreeBS_396426705802469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396848 : Nat.totient 86305482539506030728329396848 = 34810670178363876246938262528 := by
  rw [← show ((([(2, 4), (7, 1), (17, 1), (21419, 1), (2116275724223143953523, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_7, prime_seventyThreeBS_17, prime_seventyThreeBS_21419, prime_seventyThreeBS_2116275724223143953523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396849 : Nat.totient 86305482539506030728329396849 = 85123215655162447772697320736 := by
  rw [← show ((([(73, 1), (353596941947, 1), (3343543859833579, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_73, prime_seventyThreeBS_353596941947, prime_seventyThreeBS_3343543859833579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396850 : Nat.totient 86305482539506030728329396850 = 22556054450963242473866553600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (109, 1), (139, 1), (271, 1), (140131747200374013899, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_109, prime_seventyThreeBS_139, prime_seventyThreeBS_271, prime_seventyThreeBS_140131747200374013899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396851 : Nat.totient 86305482539506030728329396851 = 81763086485441750765320413000 := by
  rw [← show ((([(19, 1), (36563479, 1), (124233085639053615751, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_19, prime_seventyThreeBS_36563479, prime_seventyThreeBS_124233085639053615751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396852 : Nat.totient 86305482539506030728329396852 = 33997800459024069716566425600 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (23, 1), (103, 1), (113, 1), (2925641, 1), (192653905935083, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_11, prime_seventyThreeBS_13, prime_seventyThreeBS_23, prime_seventyThreeBS_103, prime_seventyThreeBS_113, prime_seventyThreeBS_2925641, prime_seventyThreeBS_192653905935083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396853 : Nat.totient 86305482539506030728329396853 = 57155948701659622998893640000 := by
  rw [← show ((([(3, 1), (151, 1), (190519829005532076662978801, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_151, prime_seventyThreeBS_190519829005532076662978801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396854 : Nat.totient 86305482539506030728329396854 = 40962391185526922956095691200 := by
  rw [← show ((([(2, 1), (37, 1), (41, 1), (28446104989949252052844231, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_37, prime_seventyThreeBS_41, prime_seventyThreeBS_28446104989949252052844231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396855 : Nat.totient 86305482539506030728329396855 = 59180902312804135356568729248 := by
  rw [← show ((([(5, 1), (7, 1), (2465870929700172306523697053, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_7, prime_seventyThreeBS_2465870929700172306523697053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396856 : Nat.totient 86305482539506030728329396856 = 28768494175714729805704137792 := by
  rw [← show ((([(2, 3), (3, 2), (6981604429, 1), (171692233451964787, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_6981604429, prime_seventyThreeBS_171692233451964787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396857 : Nat.totient 86305482539506030728329396857 = 86298028917997542365660332224 := by
  rw [← show ((([(11579, 1), (1384666981169, 1), (5382970440907, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_11579, prime_seventyThreeBS_1384666981169, prime_seventyThreeBS_5382970440907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396858 : Nat.totient 86305482539506030728329396858 = 43151427359900999622138536284 := by
  rw [← show ((([(2, 1), (32843, 1), (1313909852015742026129303, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_32843, prime_seventyThreeBS_1313909852015742026129303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396859 : Nat.totient 86305482539506030728329396859 = 57318212214359346641005573920 := by
  rw [← show ((([(3, 1), (263, 1), (17180399, 1), (57916171, 1), (109933054339, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_263, prime_seventyThreeBS_17180399, prime_seventyThreeBS_57916171, prime_seventyThreeBS_109933054339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396860 : Nat.totient 86305482539506030728329396860 = 33985629734933359752581283840 := by
  rw [← show ((([(2, 2), (5, 1), (67, 1), (2113, 1), (6521, 1), (4674335594937222073, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_67, prime_seventyThreeBS_2113, prime_seventyThreeBS_6521, prime_seventyThreeBS_4674335594937222073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396861 : Nat.totient 86305482539506030728329396861 = 86265170991134992076992288000 := by
  rw [← show ((([(2141, 1), (119734841, 1), (336667485971091881, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2141, prime_seventyThreeBS_119734841, prime_seventyThreeBS_336667485971091881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396862 : Nat.totient 86305482539506030728329396862 = 24658550095055592528530655840 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (163367, 1), (2984803, 1), (4214141249635511, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_7, prime_seventyThreeBS_163367, prime_seventyThreeBS_2984803, prime_seventyThreeBS_4214141249635511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396863 : Nat.totient 86305482539506030728329396863 = 78182278202127838234330692000 := by
  rw [← show ((([(11, 1), (283, 1), (8474821, 1), (3271362946754518331, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_11, prime_seventyThreeBS_283, prime_seventyThreeBS_8474821, prime_seventyThreeBS_3271362946754518331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396864 : Nat.totient 86305482539506030728329396864 = 43152741262757269858729940992 := by
  rw [← show ((([(2, 7), (6168426749, 1), (109308517353991337, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_6168426749, prime_seventyThreeBS_109308517353991337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396865 : Nat.totient 86305482539506030728329396865 = 39989508639696732104373141504 := by
  rw [← show ((([(3, 3), (5, 1), (13, 1), (17, 1), (3306983747, 1), (874742610508577, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_13, prime_seventyThreeBS_17, prime_seventyThreeBS_3306983747, prime_seventyThreeBS_874742610508577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396866 : Nat.totient 86305482539506030728329396866 = 41321946571468911263397888000 := by
  rw [← show ((([(2, 1), (31, 1), (97, 1), (5011, 1), (1235489249, 1), (2317990159621, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_31, prime_seventyThreeBS_97, prime_seventyThreeBS_5011, prime_seventyThreeBS_1235489249, prime_seventyThreeBS_2317990159621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396867 : Nat.totient 86305482539506030728329396867 = 85088224635294730711240135680 := by
  rw [← show ((([(71, 1), (50417, 1), (17376365689, 1), (1387535452829, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_71, prime_seventyThreeBS_50417, prime_seventyThreeBS_17376365689, prime_seventyThreeBS_1387535452829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396868 : Nat.totient 86305482539506030728329396868 = 28768494179835343576109798952 := by
  rw [← show ((([(2, 2), (3, 1), (7192123544958835894027449739, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_7192123544958835894027449739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396869 : Nat.totient 86305482539506030728329396869 = 73966437415923159254642691840 := by
  rw [← show ((([(7, 2), (7717, 1), (711499, 1), (216790891, 1), (1479716377, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_7, prime_seventyThreeBS_7717, prime_seventyThreeBS_711499, prime_seventyThreeBS_216790891, prime_seventyThreeBS_1479716377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396870 : Nat.totient 86305482539506030728329396870 = 31577216186511023133795088896 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (29, 1), (125029, 1), (125278351087892118253, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_19, prime_seventyThreeBS_29, prime_seventyThreeBS_125029, prime_seventyThreeBS_125278351087892118253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396871 : Nat.totient 86305482539506030728329396871 = 57536988359670687152219597912 := by
  rw [← show ((([(3, 1), (28768494179835343576109798957, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_28768494179835343576109798957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396872 : Nat.totient 86305482539506030728329396872 = 43041808771703011355664615424 := by
  rw [← show ((([(2, 3), (389, 1), (35497299197, 1), (781274204987873, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_389, prime_seventyThreeBS_35497299197, prime_seventyThreeBS_781274204987873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396873 : Nat.totient 86305482539506030728329396873 = 86286553369110030628234166400 := by
  rw [← show ((([(5581, 1), (26927, 1), (331339, 1), (1733268462857161, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5581, prime_seventyThreeBS_26927, prime_seventyThreeBS_331339, prime_seventyThreeBS_1733268462857161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396874 : Nat.totient 86305482539506030728329396874 = 26151940033499015211748546080 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (21179, 1), (16044059, 1), (1282783880918383, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_11, prime_seventyThreeBS_21179, prime_seventyThreeBS_16044059, prime_seventyThreeBS_1282783880918383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396875 : Nat.totient 86305482539506030728329396875 = 65937002286583039800760000000 := by
  rw [← show ((([(5, 5), (23, 1), (1223, 1), (1301, 1), (90053, 1), (8380281138311, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_23, prime_seventyThreeBS_1223, prime_seventyThreeBS_1301, prime_seventyThreeBS_90053, prime_seventyThreeBS_8380281138311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396876 : Nat.totient 86305482539506030728329396876 = 36945634162347904411112385600 := by
  rw [← show ((([(2, 2), (7, 1), (1427, 1), (2239, 1), (28433239, 1), (33929382163951, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_7, prime_seventyThreeBS_1427, prime_seventyThreeBS_2239, prime_seventyThreeBS_28433239, prime_seventyThreeBS_33929382163951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396877 : Nat.totient 86305482539506030728329396877 = 57536723506404684552861067040 := by
  rw [← show ((([(3, 1), (217241, 1), (132426633001299679048199, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_217241, prime_seventyThreeBS_132426633001299679048199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396878 : Nat.totient 86305482539506030728329396878 = 38985782620136930410832918496 := by
  rw [← show ((([(2, 1), (13, 1), (47, 1), (70626417790103134802233549, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_13, prime_seventyThreeBS_47, prime_seventyThreeBS_70626417790103134802233549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396879 : Nat.totient 86305482539506030728329396879 = 86305482539506030728329396878 := by
  rw [← show ((([(86305482539506030728329396879, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_86305482539506030728329396879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396880 : Nat.totient 86305482539506030728329396880 = 22474371060626401145024022528 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (43, 1), (7639, 1), (9973, 1), (109773208642563847, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_43, prime_seventyThreeBS_7639, prime_seventyThreeBS_9973, prime_seventyThreeBS_109773208642563847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396881 : Nat.totient 86305482539506030728329396881 = 85513497493109579444998571568 := by
  rw [← show ((([(179, 1), (277, 1), (1740626475596596227100607, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_179, prime_seventyThreeBS_277, prime_seventyThreeBS_1740626475596596227100607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396882 : Nat.totient 86305482539506030728329396882 = 40614344724473426225096186752 := by
  rw [← show ((([(2, 1), (17, 1), (2538396545279589139068511673, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_17, prime_seventyThreeBS_2538396545279589139068511673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396883 : Nat.totient 86305482539506030728329396883 = 49294400009319942839412019200 := by
  rw [← show ((([(3, 2), (7, 1), (2143, 1), (10164127, 1), (133583341, 1), (470818241, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_7, prime_seventyThreeBS_2143, prime_seventyThreeBS_10164127, prime_seventyThreeBS_133583341, prime_seventyThreeBS_470818241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396884 : Nat.totient 86305482539506030728329396884 = 42812943373502614550779615872 := by
  rw [← show ((([(2, 2), (127, 1), (3422437, 1), (2074441757, 1), (23929739147, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_127, prime_seventyThreeBS_3422437, prime_seventyThreeBS_2074441757, prime_seventyThreeBS_23929739147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396885 : Nat.totient 86305482539506030728329396885 = 62457496540609337757111168000 := by
  rw [← show ((([(5, 1), (11, 1), (359, 1), (557, 1), (4373, 1), (7243, 1), (247758229738351, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_5, prime_seventyThreeBS_11, prime_seventyThreeBS_359, prime_seventyThreeBS_557, prime_seventyThreeBS_4373, prime_seventyThreeBS_7243, prime_seventyThreeBS_247758229738351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396886 : Nat.totient 86305482539506030728329396886 = 28722084028352663595072307200 := by
  rw [← show ((([(2, 1), (3, 1), (881, 1), (2089, 1), (63779700889, 1), (122543507881, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_881, prime_seventyThreeBS_2089, prime_seventyThreeBS_63779700889, prime_seventyThreeBS_122543507881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396887 : Nat.totient 86305482539506030728329396887 = 86238940129846198212096244224 := by
  rw [← show ((([(1297, 1), (4908091159, 1), (13557692783891569, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_1297, prime_seventyThreeBS_4908091159, prime_seventyThreeBS_13557692783891569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396888 : Nat.totient 86305482539506030728329396888 = 43152323186277144138686653728 := by
  rw [← show ((([(2, 3), (112303, 1), (1275539, 1), (75311846938995983, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_112303, prime_seventyThreeBS_1275539, prime_seventyThreeBS_75311846938995983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396889 : Nat.totient 86305482539506030728329396889 = 54508725588503424312031946688 := by
  rw [← show ((([(3, 1), (19, 1), (378659863, 1), (761395003, 1), (5251752293, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_19, prime_seventyThreeBS_378659863, prime_seventyThreeBS_761395003, prime_seventyThreeBS_5251752293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396890 : Nat.totient 86305482539506030728329396890 = 29590287838369159502194631424 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (181183, 1), (6804918037840670224369, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_7, prime_seventyThreeBS_181183, prime_seventyThreeBS_6804918037840670224369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396891 : Nat.totient 86305482539506030728329396891 = 76640770538843559153882061824 := by
  rw [← show ((([(13, 1), (37, 1), (89, 1), (44053, 1), (45764404222215137383, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_13, prime_seventyThreeBS_37, prime_seventyThreeBS_89, prime_seventyThreeBS_44053, prime_seventyThreeBS_45764404222215137383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396892 : Nat.totient 86305482539506030728329396892 = 28768482865391750802418930560 := by
  rw [← show ((([(2, 2), (3, 3), (2807561, 1), (26945647, 1), (10563231860947, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_2807561, prime_seventyThreeBS_26945647, prime_seventyThreeBS_10563231860947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396893 : Nat.totient 86305482539506030728329396893 = 86305454731229524283136873840 := by
  rw [← show ((([(3114317, 1), (901056859, 1), (30755541062531, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3114317, prime_seventyThreeBS_901056859, prime_seventyThreeBS_30755541062531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396894 : Nat.totient 86305482539506030728329396894 = 43106379674430829945499967040 := by
  rw [← show ((([(2, 1), (947, 1), (54323, 1), (192246521, 1), (4363311062447, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_947, prime_seventyThreeBS_54323, prime_seventyThreeBS_192246521, prime_seventyThreeBS_4363311062447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396895 : Nat.totient 86305482539506030728329396895 = 44906917096567485175451648000 := by
  rw [← show ((([(3, 1), (5, 1), (41, 1), (69347273, 1), (2023642918884731201, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_5, prime_seventyThreeBS_41, prime_seventyThreeBS_69347273, prime_seventyThreeBS_2023642918884731201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396896 : Nat.totient 86305482539506030728329396896 = 39229764790684559421967907520 := by
  rw [← show ((([(2, 5), (11, 1), (245186029941778496387299423, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_11, prime_seventyThreeBS_245186029941778496387299423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396897 : Nat.totient 86305482539506030728329396897 = 68831088009754425325269811200 := by
  rw [← show ((([(7, 1), (31, 1), (53, 1), (83, 1), (229, 1), (269, 1), (38273, 1), (1615403, 1), (23739061, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_7, prime_seventyThreeBS_31, prime_seventyThreeBS_53, prime_seventyThreeBS_83, prime_seventyThreeBS_229, prime_seventyThreeBS_269, prime_seventyThreeBS_38273, prime_seventyThreeBS_1615403, prime_seventyThreeBS_23739061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396898 : Nat.totient 86305482539506030728329396898 = 26946030625730953788001370112 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (59, 1), (257, 1), (102180570803, 1), (403650820189, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_3, prime_seventyThreeBS_23, prime_seventyThreeBS_59, prime_seventyThreeBS_257, prime_seventyThreeBS_102180570803, prime_seventyThreeBS_403650820189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396899 : Nat.totient 86305482539506030728329396899 = 78373723763827117099342471680 := by
  rw [← show ((([(17, 1), (29, 1), (1453, 1), (120483021823081336548331, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_17, prime_seventyThreeBS_29, prime_seventyThreeBS_1453, prime_seventyThreeBS_120483021823081336548331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396900 : Nat.totient 86305482539506030728329396900 = 34409742875685792055855095840 := by
  rw [← show ((([(2, 2), (5, 2), (307, 1), (2811253502915505886916267, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_5, prime_seventyThreeBS_307, prime_seventyThreeBS_2811253502915505886916267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396901 : Nat.totient 86305482539506030728329396901 = 56412948310534502880089495040 := by
  rw [← show ((([(3, 2), (61, 1), (313, 1), (502252032679260175214473, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_3, prime_seventyThreeBS_61, prime_seventyThreeBS_313, prime_seventyThreeBS_502252032679260175214473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396902 : Nat.totient 86305482539506030728329396902 = 43152741269753015364164698450 := by
  rw [← show ((([(2, 1), (43152741269753015364164698451, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396902 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_2, prime_seventyThreeBS_43152741269753015364164698451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyThreeBS_86305482539506030728329396903 : Nat.totient 86305482539506030728329396903 = 85934879371253531766650900544 := by
  rw [← show ((([(233, 1), (444403, 1), (833499765543645825397, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506030728329396903 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyThreeBS_233, prime_seventyThreeBS_444403, prime_seventyThreeBS_833499765543645825397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyThreeBS : certifiedKill 3 86305482539506030728329396799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyThreeBS_86305482539506030728329396800, phi_seventyThreeBS_86305482539506030728329396801, phi_seventyThreeBS_86305482539506030728329396802,
    phi_seventyThreeBS_86305482539506030728329396803, phi_seventyThreeBS_86305482539506030728329396804, phi_seventyThreeBS_86305482539506030728329396805,
    phi_seventyThreeBS_86305482539506030728329396806, phi_seventyThreeBS_86305482539506030728329396807, phi_seventyThreeBS_86305482539506030728329396808,
    phi_seventyThreeBS_86305482539506030728329396809, phi_seventyThreeBS_86305482539506030728329396810, phi_seventyThreeBS_86305482539506030728329396811,
    phi_seventyThreeBS_86305482539506030728329396812, phi_seventyThreeBS_86305482539506030728329396813, phi_seventyThreeBS_86305482539506030728329396814,
    phi_seventyThreeBS_86305482539506030728329396815, phi_seventyThreeBS_86305482539506030728329396816, phi_seventyThreeBS_86305482539506030728329396817,
    phi_seventyThreeBS_86305482539506030728329396818, phi_seventyThreeBS_86305482539506030728329396819, phi_seventyThreeBS_86305482539506030728329396820,
    phi_seventyThreeBS_86305482539506030728329396821, phi_seventyThreeBS_86305482539506030728329396822, phi_seventyThreeBS_86305482539506030728329396823,
    phi_seventyThreeBS_86305482539506030728329396824, phi_seventyThreeBS_86305482539506030728329396825, phi_seventyThreeBS_86305482539506030728329396826,
    phi_seventyThreeBS_86305482539506030728329396827, phi_seventyThreeBS_86305482539506030728329396828, phi_seventyThreeBS_86305482539506030728329396829,
    phi_seventyThreeBS_86305482539506030728329396830, phi_seventyThreeBS_86305482539506030728329396831, phi_seventyThreeBS_86305482539506030728329396832,
    phi_seventyThreeBS_86305482539506030728329396833, phi_seventyThreeBS_86305482539506030728329396834, phi_seventyThreeBS_86305482539506030728329396835,
    phi_seventyThreeBS_86305482539506030728329396836, phi_seventyThreeBS_86305482539506030728329396837, phi_seventyThreeBS_86305482539506030728329396838,
    phi_seventyThreeBS_86305482539506030728329396839, phi_seventyThreeBS_86305482539506030728329396840, phi_seventyThreeBS_86305482539506030728329396841,
    phi_seventyThreeBS_86305482539506030728329396842, phi_seventyThreeBS_86305482539506030728329396843, phi_seventyThreeBS_86305482539506030728329396844,
    phi_seventyThreeBS_86305482539506030728329396845, phi_seventyThreeBS_86305482539506030728329396846, phi_seventyThreeBS_86305482539506030728329396847,
    phi_seventyThreeBS_86305482539506030728329396848, phi_seventyThreeBS_86305482539506030728329396849, phi_seventyThreeBS_86305482539506030728329396850,
    phi_seventyThreeBS_86305482539506030728329396851, phi_seventyThreeBS_86305482539506030728329396852, phi_seventyThreeBS_86305482539506030728329396853,
    phi_seventyThreeBS_86305482539506030728329396854, phi_seventyThreeBS_86305482539506030728329396855, phi_seventyThreeBS_86305482539506030728329396856,
    phi_seventyThreeBS_86305482539506030728329396857, phi_seventyThreeBS_86305482539506030728329396858, phi_seventyThreeBS_86305482539506030728329396859,
    phi_seventyThreeBS_86305482539506030728329396860, phi_seventyThreeBS_86305482539506030728329396861, phi_seventyThreeBS_86305482539506030728329396862,
    phi_seventyThreeBS_86305482539506030728329396863, phi_seventyThreeBS_86305482539506030728329396864, phi_seventyThreeBS_86305482539506030728329396865,
    phi_seventyThreeBS_86305482539506030728329396866, phi_seventyThreeBS_86305482539506030728329396867, phi_seventyThreeBS_86305482539506030728329396868,
    phi_seventyThreeBS_86305482539506030728329396869, phi_seventyThreeBS_86305482539506030728329396870, phi_seventyThreeBS_86305482539506030728329396871,
    phi_seventyThreeBS_86305482539506030728329396872, phi_seventyThreeBS_86305482539506030728329396873, phi_seventyThreeBS_86305482539506030728329396874,
    phi_seventyThreeBS_86305482539506030728329396875, phi_seventyThreeBS_86305482539506030728329396876, phi_seventyThreeBS_86305482539506030728329396877,
    phi_seventyThreeBS_86305482539506030728329396878, phi_seventyThreeBS_86305482539506030728329396879, phi_seventyThreeBS_86305482539506030728329396880,
    phi_seventyThreeBS_86305482539506030728329396881, phi_seventyThreeBS_86305482539506030728329396882, phi_seventyThreeBS_86305482539506030728329396883,
    phi_seventyThreeBS_86305482539506030728329396884, phi_seventyThreeBS_86305482539506030728329396885, phi_seventyThreeBS_86305482539506030728329396886,
    phi_seventyThreeBS_86305482539506030728329396887, phi_seventyThreeBS_86305482539506030728329396888, phi_seventyThreeBS_86305482539506030728329396889,
    phi_seventyThreeBS_86305482539506030728329396890, phi_seventyThreeBS_86305482539506030728329396891, phi_seventyThreeBS_86305482539506030728329396892,
    phi_seventyThreeBS_86305482539506030728329396893, phi_seventyThreeBS_86305482539506030728329396894, phi_seventyThreeBS_86305482539506030728329396895,
    phi_seventyThreeBS_86305482539506030728329396896, phi_seventyThreeBS_86305482539506030728329396897, phi_seventyThreeBS_86305482539506030728329396898,
    phi_seventyThreeBS_86305482539506030728329396899, phi_seventyThreeBS_86305482539506030728329396900, phi_seventyThreeBS_86305482539506030728329396901,
    phi_seventyThreeBS_86305482539506030728329396902, phi_seventyThreeBS_86305482539506030728329396903]

end TotientTailPeriodKiller
end Erdos249257
