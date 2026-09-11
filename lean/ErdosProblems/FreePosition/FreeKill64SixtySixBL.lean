import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 66P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtySixBLFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtySixBLFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtySixBLFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtySixBLFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtySixBLFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtySixBLFastPow a n * sixtySixBLFastPow a n * a
        else sixtySixBLFastPow a n * sixtySixBLFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtySixBL_2 : Nat.Prime 2 := by norm_num

private theorem prime_sixtySixBL_3 : Nat.Prime 3 := by norm_num

private theorem prime_sixtySixBL_5 : Nat.Prime 5 := by norm_num

private theorem prime_sixtySixBL_7 : Nat.Prime 7 := by norm_num

private theorem prime_sixtySixBL_11 : Nat.Prime 11 := by norm_num

private theorem prime_sixtySixBL_13 : Nat.Prime 13 := by norm_num

private theorem prime_sixtySixBL_17 : Nat.Prime 17 := by norm_num

private theorem prime_sixtySixBL_19 : Nat.Prime 19 := by norm_num

private theorem prime_sixtySixBL_23 : Nat.Prime 23 := by norm_num

private theorem prime_sixtySixBL_29 : Nat.Prime 29 := by norm_num

private theorem prime_sixtySixBL_31 : Nat.Prime 31 := by norm_num

private theorem prime_sixtySixBL_37 : Nat.Prime 37 := by norm_num

private theorem prime_sixtySixBL_41 : Nat.Prime 41 := by norm_num

private theorem prime_sixtySixBL_43 : Nat.Prime 43 := by norm_num

private theorem prime_sixtySixBL_47 : Nat.Prime 47 := by norm_num

private theorem prime_sixtySixBL_53 : Nat.Prime 53 := by norm_num

private theorem prime_sixtySixBL_59 : Nat.Prime 59 := by norm_num

private theorem prime_sixtySixBL_61 : Nat.Prime 61 := by norm_num

private theorem prime_sixtySixBL_67 : Nat.Prime 67 := by norm_num

private theorem prime_sixtySixBL_71 : Nat.Prime 71 := by norm_num

private theorem prime_sixtySixBL_73 : Nat.Prime 73 := by norm_num

private theorem prime_sixtySixBL_79 : Nat.Prime 79 := by norm_num

private theorem prime_sixtySixBL_83 : Nat.Prime 83 := by norm_num

private theorem prime_sixtySixBL_89 : Nat.Prime 89 := by norm_num

private theorem prime_sixtySixBL_97 : Nat.Prime 97 := by norm_num

private theorem prime_sixtySixBL_101 : Nat.Prime 101 := by norm_num

private theorem prime_sixtySixBL_103 : Nat.Prime 103 := by norm_num

private theorem prime_sixtySixBL_107 : Nat.Prime 107 := by norm_num

private theorem prime_sixtySixBL_109 : Nat.Prime 109 := by norm_num

private theorem prime_sixtySixBL_113 : Nat.Prime 113 := by norm_num

private theorem prime_sixtySixBL_127 : Nat.Prime 127 := by norm_num

private theorem prime_sixtySixBL_131 : Nat.Prime 131 := by norm_num

private theorem prime_sixtySixBL_137 : Nat.Prime 137 := by norm_num

private theorem prime_sixtySixBL_149 : Nat.Prime 149 := by norm_num

private theorem prime_sixtySixBL_151 : Nat.Prime 151 := by norm_num

private theorem prime_sixtySixBL_157 : Nat.Prime 157 := by norm_num

private theorem prime_sixtySixBL_163 : Nat.Prime 163 := by norm_num

private theorem prime_sixtySixBL_167 : Nat.Prime 167 := by norm_num

private theorem prime_sixtySixBL_173 : Nat.Prime 173 := by norm_num

private theorem prime_sixtySixBL_179 : Nat.Prime 179 := by norm_num

private theorem prime_sixtySixBL_181 : Nat.Prime 181 := by norm_num

private theorem prime_sixtySixBL_191 : Nat.Prime 191 := by norm_num

private theorem prime_sixtySixBL_197 : Nat.Prime 197 := by norm_num

private theorem prime_sixtySixBL_199 : Nat.Prime 199 := by norm_num

private theorem prime_sixtySixBL_211 : Nat.Prime 211 := by norm_num

private theorem prime_sixtySixBL_223 : Nat.Prime 223 := by norm_num

private theorem prime_sixtySixBL_227 : Nat.Prime 227 := by norm_num

private theorem prime_sixtySixBL_229 : Nat.Prime 229 := by norm_num

private theorem prime_sixtySixBL_233 : Nat.Prime 233 := by norm_num

private theorem prime_sixtySixBL_239 : Nat.Prime 239 := by norm_num

private theorem prime_sixtySixBL_241 : Nat.Prime 241 := by norm_num

private theorem prime_sixtySixBL_251 : Nat.Prime 251 := by norm_num

private theorem prime_sixtySixBL_257 : Nat.Prime 257 := by norm_num

private theorem prime_sixtySixBL_281 : Nat.Prime 281 := by norm_num

private theorem prime_sixtySixBL_293 : Nat.Prime 293 := by norm_num

private theorem prime_sixtySixBL_307 : Nat.Prime 307 := by norm_num

private theorem prime_sixtySixBL_311 : Nat.Prime 311 := by norm_num

private theorem prime_sixtySixBL_331 : Nat.Prime 331 := by norm_num

private theorem prime_sixtySixBL_349 : Nat.Prime 349 := by norm_num

private theorem prime_sixtySixBL_353 : Nat.Prime 353 := by norm_num

private theorem prime_sixtySixBL_367 : Nat.Prime 367 := by norm_num

private theorem prime_sixtySixBL_379 : Nat.Prime 379 := by norm_num

private theorem prime_sixtySixBL_383 : Nat.Prime 383 := by norm_num

private theorem prime_sixtySixBL_389 : Nat.Prime 389 := by norm_num

private theorem prime_sixtySixBL_397 : Nat.Prime 397 := by norm_num

private theorem prime_sixtySixBL_401 : Nat.Prime 401 := by norm_num

private theorem prime_sixtySixBL_419 : Nat.Prime 419 := by norm_num

private theorem prime_sixtySixBL_421 : Nat.Prime 421 := by norm_num

private theorem prime_sixtySixBL_431 : Nat.Prime 431 := by norm_num

private theorem prime_sixtySixBL_433 : Nat.Prime 433 := by norm_num

private theorem prime_sixtySixBL_443 : Nat.Prime 443 := by norm_num

private theorem prime_sixtySixBL_449 : Nat.Prime 449 := by norm_num

private theorem prime_sixtySixBL_463 : Nat.Prime 463 := by norm_num

private theorem prime_sixtySixBL_499 : Nat.Prime 499 := by norm_num

private theorem prime_sixtySixBL_503 : Nat.Prime 503 := by norm_num

private theorem prime_sixtySixBL_521 : Nat.Prime 521 := by norm_num

private theorem prime_sixtySixBL_557 : Nat.Prime 557 := by norm_num

private theorem prime_sixtySixBL_569 : Nat.Prime 569 := by norm_num

private theorem prime_sixtySixBL_571 : Nat.Prime 571 := by norm_num

private theorem prime_sixtySixBL_577 : Nat.Prime 577 := by norm_num

private theorem prime_sixtySixBL_587 : Nat.Prime 587 := by norm_num

private theorem prime_sixtySixBL_613 : Nat.Prime 613 := by norm_num

private theorem prime_sixtySixBL_643 : Nat.Prime 643 := by norm_num

private theorem prime_sixtySixBL_653 : Nat.Prime 653 := by norm_num

private theorem prime_sixtySixBL_659 : Nat.Prime 659 := by norm_num

private theorem prime_sixtySixBL_661 : Nat.Prime 661 := by norm_num

private theorem prime_sixtySixBL_673 : Nat.Prime 673 := by norm_num

private theorem prime_sixtySixBL_691 : Nat.Prime 691 := by norm_num

private theorem prime_sixtySixBL_719 : Nat.Prime 719 := by norm_num

private theorem prime_sixtySixBL_739 : Nat.Prime 739 := by norm_num

private theorem prime_sixtySixBL_761 : Nat.Prime 761 := by norm_num

private theorem prime_sixtySixBL_797 : Nat.Prime 797 := by norm_num

private theorem prime_sixtySixBL_809 : Nat.Prime 809 := by norm_num

private theorem prime_sixtySixBL_811 : Nat.Prime 811 := by norm_num

private theorem prime_sixtySixBL_823 : Nat.Prime 823 := by norm_num

private theorem prime_sixtySixBL_829 : Nat.Prime 829 := by norm_num

private theorem prime_sixtySixBL_853 : Nat.Prime 853 := by norm_num

private theorem prime_sixtySixBL_859 : Nat.Prime 859 := by norm_num

private theorem prime_sixtySixBL_863 : Nat.Prime 863 := by norm_num

private theorem prime_sixtySixBL_887 : Nat.Prime 887 := by norm_num

private theorem prime_sixtySixBL_907 : Nat.Prime 907 := by norm_num

private theorem prime_sixtySixBL_919 : Nat.Prime 919 := by norm_num

private theorem prime_sixtySixBL_929 : Nat.Prime 929 := by norm_num

private theorem prime_sixtySixBL_971 : Nat.Prime 971 := by norm_num

private theorem prime_sixtySixBL_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_sixtySixBL_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_sixtySixBL_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_sixtySixBL_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_sixtySixBL_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_sixtySixBL_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_sixtySixBL_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_sixtySixBL_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_sixtySixBL_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_sixtySixBL_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_sixtySixBL_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_sixtySixBL_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_sixtySixBL_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_sixtySixBL_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_sixtySixBL_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_sixtySixBL_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_sixtySixBL_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_sixtySixBL_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_sixtySixBL_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_sixtySixBL_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_sixtySixBL_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_sixtySixBL_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_sixtySixBL_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_sixtySixBL_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_sixtySixBL_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_sixtySixBL_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_sixtySixBL_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_sixtySixBL_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_sixtySixBL_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_sixtySixBL_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_sixtySixBL_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_sixtySixBL_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_sixtySixBL_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_sixtySixBL_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_sixtySixBL_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_sixtySixBL_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_sixtySixBL_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_sixtySixBL_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_sixtySixBL_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_sixtySixBL_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_sixtySixBL_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_sixtySixBL_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_sixtySixBL_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_sixtySixBL_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_sixtySixBL_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_sixtySixBL_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_sixtySixBL_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_sixtySixBL_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_sixtySixBL_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_sixtySixBL_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_sixtySixBL_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_sixtySixBL_3853 : Nat.Prime 3853 := by norm_num

private theorem prime_sixtySixBL_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_sixtySixBL_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_sixtySixBL_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_sixtySixBL_4229 : Nat.Prime 4229 := by norm_num

private theorem prime_sixtySixBL_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_sixtySixBL_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_sixtySixBL_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_sixtySixBL_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_sixtySixBL_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_sixtySixBL_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_sixtySixBL_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_sixtySixBL_5099 : Nat.Prime 5099 := by norm_num

private theorem prime_sixtySixBL_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_sixtySixBL_5147 : Nat.Prime 5147 := by norm_num

private theorem prime_sixtySixBL_5393 : Nat.Prime 5393 := by norm_num

private theorem prime_sixtySixBL_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_sixtySixBL_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_sixtySixBL_5483 : Nat.Prime 5483 := by norm_num

private theorem prime_sixtySixBL_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_sixtySixBL_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_sixtySixBL_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_sixtySixBL_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_sixtySixBL_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_sixtySixBL_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_sixtySixBL_6091 : Nat.Prime 6091 := by norm_num

private theorem prime_sixtySixBL_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_sixtySixBL_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_sixtySixBL_7219 : Nat.Prime 7219 := by norm_num

private theorem prime_sixtySixBL_7393 : Nat.Prime 7393 := by norm_num

private theorem prime_sixtySixBL_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_sixtySixBL_7549 : Nat.Prime 7549 := by norm_num

private theorem prime_sixtySixBL_7949 : Nat.Prime 7949 := by norm_num

private theorem prime_sixtySixBL_7951 : Nat.Prime 7951 := by norm_num

private theorem prime_sixtySixBL_8011 : Nat.Prime 8011 := by norm_num

private theorem prime_sixtySixBL_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_sixtySixBL_8467 : Nat.Prime 8467 := by norm_num

private theorem prime_sixtySixBL_8641 : Nat.Prime 8641 := by norm_num

private theorem prime_sixtySixBL_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_sixtySixBL_8681 : Nat.Prime 8681 := by norm_num

private theorem prime_sixtySixBL_8867 : Nat.Prime 8867 := by norm_num

private theorem prime_sixtySixBL_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_sixtySixBL_10477 : Nat.Prime 10477 := by norm_num

private theorem prime_sixtySixBL_10753 : Nat.Prime 10753 := by norm_num

private theorem prime_sixtySixBL_10973 : Nat.Prime 10973 := by norm_num

private theorem prime_sixtySixBL_11059 : Nat.Prime 11059 := by norm_num

private theorem prime_sixtySixBL_11701 : Nat.Prime 11701 := by norm_num

private theorem prime_sixtySixBL_12347 : Nat.Prime 12347 := by norm_num

private theorem prime_sixtySixBL_12527 : Nat.Prime 12527 := by norm_num

private theorem prime_sixtySixBL_12577 : Nat.Prime 12577 := by norm_num

private theorem prime_sixtySixBL_12743 : Nat.Prime 12743 := by norm_num

private theorem prime_sixtySixBL_13009 : Nat.Prime 13009 := by norm_num

private theorem prime_sixtySixBL_13183 : Nat.Prime 13183 := by norm_num

private theorem prime_sixtySixBL_14741 : Nat.Prime 14741 := by norm_num

private theorem prime_sixtySixBL_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_sixtySixBL_15619 : Nat.Prime 15619 := by norm_num

private theorem prime_sixtySixBL_16033 : Nat.Prime 16033 := by norm_num

private theorem prime_sixtySixBL_16069 : Nat.Prime 16069 := by norm_num

private theorem prime_sixtySixBL_16139 : Nat.Prime 16139 := by norm_num

private theorem prime_sixtySixBL_16633 : Nat.Prime 16633 := by norm_num

private theorem prime_sixtySixBL_16747 : Nat.Prime 16747 := by norm_num

private theorem prime_sixtySixBL_18521 : Nat.Prime 18521 := by norm_num

private theorem prime_sixtySixBL_18701 : Nat.Prime 18701 := by norm_num

private theorem prime_sixtySixBL_20113 : Nat.Prime 20113 := by norm_num

private theorem prime_sixtySixBL_20347 : Nat.Prime 20347 := by norm_num

private theorem prime_sixtySixBL_20549 : Nat.Prime 20549 := by norm_num

private theorem prime_sixtySixBL_21059 : Nat.Prime 21059 := by norm_num

private theorem prime_sixtySixBL_21737 : Nat.Prime 21737 := by norm_num

private theorem prime_sixtySixBL_23509 : Nat.Prime 23509 := by norm_num

private theorem prime_sixtySixBL_24239 : Nat.Prime 24239 := by norm_num

private theorem prime_sixtySixBL_26171 : Nat.Prime 26171 := by norm_num

private theorem prime_sixtySixBL_26863 : Nat.Prime 26863 := by norm_num

private theorem prime_sixtySixBL_27281 : Nat.Prime 27281 := by norm_num

private theorem prime_sixtySixBL_28759 : Nat.Prime 28759 := by norm_num

private theorem prime_sixtySixBL_30637 : Nat.Prime 30637 := by norm_num

private theorem prime_sixtySixBL_31223 : Nat.Prime 31223 := by norm_num

private theorem prime_sixtySixBL_34849 : Nat.Prime 34849 := by norm_num

private theorem prime_sixtySixBL_34871 : Nat.Prime 34871 := by norm_num

private theorem prime_sixtySixBL_35419 : Nat.Prime 35419 := by norm_num

private theorem prime_sixtySixBL_37087 : Nat.Prime 37087 := by norm_num

private theorem prime_sixtySixBL_37747 : Nat.Prime 37747 := by norm_num

private theorem prime_sixtySixBL_39191 : Nat.Prime 39191 := by norm_num

private theorem prime_sixtySixBL_39461 : Nat.Prime 39461 := by norm_num

private theorem prime_sixtySixBL_40241 : Nat.Prime 40241 := by norm_num

private theorem prime_sixtySixBL_43669 : Nat.Prime 43669 := by norm_num

private theorem prime_sixtySixBL_46093 : Nat.Prime 46093 := by norm_num

private theorem prime_sixtySixBL_48187 : Nat.Prime 48187 := by norm_num

private theorem prime_sixtySixBL_51197 : Nat.Prime 51197 := by norm_num

private theorem prime_sixtySixBL_54443 : Nat.Prime 54443 := by norm_num

private theorem prime_sixtySixBL_54541 : Nat.Prime 54541 := by norm_num

private theorem prime_sixtySixBL_55051 : Nat.Prime 55051 := by norm_num

private theorem prime_sixtySixBL_55661 : Nat.Prime 55661 := by norm_num

private theorem prime_sixtySixBL_58153 : Nat.Prime 58153 := by norm_num

private theorem prime_sixtySixBL_62351 : Nat.Prime 62351 := by norm_num

private theorem prime_sixtySixBL_65731 : Nat.Prime 65731 := by norm_num

private theorem prime_sixtySixBL_70067 : Nat.Prime 70067 := by norm_num

private theorem prime_sixtySixBL_71909 : Nat.Prime 71909 := by norm_num

private theorem prime_sixtySixBL_72689 : Nat.Prime 72689 := by norm_num

private theorem prime_sixtySixBL_73133 : Nat.Prime 73133 := by norm_num

private theorem prime_sixtySixBL_86183 : Nat.Prime 86183 := by norm_num

private theorem prime_sixtySixBL_87013 : Nat.Prime 87013 := by norm_num

private theorem prime_sixtySixBL_88169 : Nat.Prime 88169 := by norm_num

private theorem prime_sixtySixBL_89273 : Nat.Prime 89273 := by norm_num

private theorem prime_sixtySixBL_93581 : Nat.Prime 93581 := by norm_num

private theorem prime_sixtySixBL_100363 : Nat.Prime 100363 := by norm_num

private theorem prime_sixtySixBL_103483 : Nat.Prime 103483 := by norm_num

private theorem prime_sixtySixBL_112543 : Nat.Prime 112543 := by norm_num

private theorem prime_sixtySixBL_116539 : Nat.Prime 116539 := by norm_num

private theorem prime_sixtySixBL_121501 : Nat.Prime 121501 := by norm_num

private theorem prime_sixtySixBL_124541 : Nat.Prime 124541 := by norm_num

private theorem prime_sixtySixBL_126041 : Nat.Prime 126041 := by norm_num

private theorem prime_sixtySixBL_127807 : Nat.Prime 127807 := by norm_num

private theorem prime_sixtySixBL_143291 : Nat.Prime 143291 := by norm_num

private theorem prime_sixtySixBL_148279 : Nat.Prime 148279 := by norm_num

private theorem prime_sixtySixBL_155009 : Nat.Prime 155009 := by norm_num

private theorem prime_sixtySixBL_164581 : Nat.Prime 164581 := by norm_num

private theorem prime_sixtySixBL_164617 : Nat.Prime 164617 := by norm_num

private theorem prime_sixtySixBL_166919 : Nat.Prime 166919 := by norm_num

private theorem prime_sixtySixBL_178757 : Nat.Prime 178757 := by norm_num

private theorem prime_sixtySixBL_179779 : Nat.Prime 179779 := by norm_num

private theorem prime_sixtySixBL_189613 : Nat.Prime 189613 := by norm_num

private theorem prime_sixtySixBL_190301 : Nat.Prime 190301 := by norm_num

private theorem prime_sixtySixBL_192319 : Nat.Prime 192319 := by norm_num

private theorem prime_sixtySixBL_195043 : Nat.Prime 195043 := by norm_num

private theorem prime_sixtySixBL_226601 : Nat.Prime 226601 := by norm_num

private theorem prime_sixtySixBL_231131 : Nat.Prime 231131 := by norm_num

private theorem prime_sixtySixBL_251467 : Nat.Prime 251467 := by norm_num

private theorem prime_sixtySixBL_256363 : Nat.Prime 256363 := by norm_num

private theorem prime_sixtySixBL_258809 : Nat.Prime 258809 := by norm_num

private theorem prime_sixtySixBL_267637 : Nat.Prime 267637 := by norm_num

private theorem prime_sixtySixBL_299501 : Nat.Prime 299501 := by norm_num

private theorem prime_sixtySixBL_306577 : Nat.Prime 306577 := by norm_num

private theorem prime_sixtySixBL_307873 : Nat.Prime 307873 := by norm_num

private theorem prime_sixtySixBL_310181 : Nat.Prime 310181 := by norm_num

private theorem prime_sixtySixBL_322573 : Nat.Prime 322573 := by norm_num

private theorem prime_sixtySixBL_326323 : Nat.Prime 326323 := by norm_num

private theorem prime_sixtySixBL_335341 : Nat.Prime 335341 := by norm_num

private theorem prime_sixtySixBL_342553 : Nat.Prime 342553 := by norm_num

private theorem prime_sixtySixBL_351551 : Nat.Prime 351551 := by norm_num

private theorem prime_sixtySixBL_380459 : Nat.Prime 380459 := by norm_num

private theorem prime_sixtySixBL_395543 : Nat.Prime 395543 := by norm_num

private theorem prime_sixtySixBL_409153 : Nat.Prime 409153 := by norm_num

private theorem prime_sixtySixBL_438133 : Nat.Prime 438133 := by norm_num

private theorem prime_sixtySixBL_445649 : Nat.Prime 445649 := by norm_num

private theorem prime_sixtySixBL_452689 : Nat.Prime 452689 := by norm_num

private theorem prime_sixtySixBL_489109 : Nat.Prime 489109 := by norm_num

private theorem prime_sixtySixBL_490741 : Nat.Prime 490741 := by norm_num

private theorem prime_sixtySixBL_521023 : Nat.Prime 521023 := by norm_num

private theorem prime_sixtySixBL_534101 : Nat.Prime 534101 := by norm_num

private theorem prime_sixtySixBL_551113 : Nat.Prime 551113 := by norm_num

private theorem prime_sixtySixBL_563113 : Nat.Prime 563113 := by norm_num

private theorem prime_sixtySixBL_594313 : Nat.Prime 594313 := by norm_num

private theorem prime_sixtySixBL_617681 : Nat.Prime 617681 := by norm_num

private theorem prime_sixtySixBL_644227 : Nat.Prime 644227 := by norm_num

private theorem prime_sixtySixBL_666901 : Nat.Prime 666901 := by norm_num

private theorem prime_sixtySixBL_682411 : Nat.Prime 682411 := by norm_num

private theorem prime_sixtySixBL_701621 : Nat.Prime 701621 := by norm_num

private theorem prime_sixtySixBL_757429 : Nat.Prime 757429 := by norm_num

private theorem prime_sixtySixBL_808153 : Nat.Prime 808153 := by norm_num

private theorem prime_sixtySixBL_858241 : Nat.Prime 858241 := by norm_num

private theorem prime_sixtySixBL_924557 : Nat.Prime 924557 := by norm_num

private theorem prime_sixtySixBL_930689 : Nat.Prime 930689 := by norm_num

private theorem prime_sixtySixBL_953873 : Nat.Prime 953873 := by norm_num

private theorem prime_sixtySixBL_958193 : Nat.Prime 958193 := by norm_num

private theorem prime_sixtySixBL_974971 : Nat.Prime 974971 := by norm_num

private theorem prime_sixtySixBL_979327 : Nat.Prime 979327 := by norm_num

private theorem prime_sixtySixBL_980831 : Nat.Prime 980831 := by norm_num

private theorem prime_sixtySixBL_986191 : Nat.Prime 986191 := by norm_num

private theorem prime_sixtySixBL_1006853 : Nat.Prime 1006853 := by norm_num

private theorem prime_sixtySixBL_1131121 : Nat.Prime 1131121 := by norm_num

private theorem prime_sixtySixBL_1151209 : Nat.Prime 1151209 := by norm_num

private theorem prime_sixtySixBL_1187141 : Nat.Prime 1187141 := by norm_num

private theorem prime_sixtySixBL_1312169 : Nat.Prime 1312169 := by norm_num

private theorem prime_sixtySixBL_1372139 : Nat.Prime 1372139 := by norm_num

private theorem prime_sixtySixBL_1425299 : Nat.Prime 1425299 := by norm_num

private theorem prime_sixtySixBL_1517651 : Nat.Prime 1517651 := by norm_num

private theorem prime_sixtySixBL_1552451 : Nat.Prime 1552451 := by norm_num

private theorem prime_sixtySixBL_1577699 : Nat.Prime 1577699 := by norm_num

private theorem prime_sixtySixBL_1652459 : Nat.Prime 1652459 := by norm_num

private theorem prime_sixtySixBL_1878887 : Nat.Prime 1878887 := by norm_num

private theorem prime_sixtySixBL_1945061 : Nat.Prime 1945061 := by norm_num

private theorem prime_sixtySixBL_1970183 : Nat.Prime 1970183 := by norm_num

private theorem prime_sixtySixBL_2215547 : Nat.Prime 2215547 := by norm_num

private theorem prime_sixtySixBL_2328617 : Nat.Prime 2328617 := by norm_num

private theorem prime_sixtySixBL_2340769 : Nat.Prime 2340769 := by norm_num

private theorem prime_sixtySixBL_2518069 : Nat.Prime 2518069 := by norm_num

private theorem prime_sixtySixBL_2661413 : Nat.Prime 2661413 := by norm_num

private theorem prime_sixtySixBL_2721013 : Nat.Prime 2721013 := by norm_num

private theorem prime_sixtySixBL_2747273 : Nat.Prime 2747273 := by norm_num

private theorem prime_sixtySixBL_2880467 : Nat.Prime 2880467 := by norm_num

private theorem prime_sixtySixBL_2934233 : Nat.Prime 2934233 := by norm_num

private theorem prime_sixtySixBL_2988373 : Nat.Prime 2988373 := by norm_num

private theorem prime_sixtySixBL_3165661 : Nat.Prime 3165661 := by norm_num

private theorem prime_sixtySixBL_3178421 : Nat.Prime 3178421 := by norm_num

private theorem prime_sixtySixBL_3434581 : Nat.Prime 3434581 := by norm_num

private theorem prime_sixtySixBL_3694711 : Nat.Prime 3694711 := by norm_num

private theorem prime_sixtySixBL_3824651 : Nat.Prime 3824651 := by norm_num

private theorem prime_sixtySixBL_4002727 : Nat.Prime 4002727 := by norm_num

private theorem prime_sixtySixBL_4133971 : Nat.Prime 4133971 := by norm_num

private theorem prime_sixtySixBL_4419271 : Nat.Prime 4419271 := by norm_num

private theorem prime_sixtySixBL_4527517 : Nat.Prime 4527517 := by norm_num

private theorem prime_sixtySixBL_4816751 : Nat.Prime 4816751 := by norm_num

private theorem prime_sixtySixBL_4880087 : Nat.Prime 4880087 := by norm_num

private theorem prime_sixtySixBL_5089741 : Nat.Prime 5089741 := by norm_num

private theorem prime_sixtySixBL_5215393 : Nat.Prime 5215393 := by norm_num

private theorem prime_sixtySixBL_5264873 : Nat.Prime 5264873 := by norm_num

private theorem prime_sixtySixBL_5517013 : Nat.Prime 5517013 := by norm_num

private theorem prime_sixtySixBL_5620481 : Nat.Prime 5620481 := by norm_num

private theorem prime_sixtySixBL_6126347 : Nat.Prime 6126347 := by norm_num

private theorem prime_sixtySixBL_6525301 : Nat.Prime 6525301 := by norm_num

private theorem prime_sixtySixBL_7061281 : Nat.Prime 7061281 := by norm_num

private theorem prime_sixtySixBL_7353497 : Nat.Prime 7353497 := by norm_num

private theorem prime_sixtySixBL_7460699 : Nat.Prime 7460699 := by norm_num

private theorem prime_sixtySixBL_8686159 : Nat.Prime 8686159 := by norm_num

private theorem prime_sixtySixBL_9067567 : Nat.Prime 9067567 := by norm_num

private theorem prime_sixtySixBL_9714277 : Nat.Prime 9714277 := by norm_num

private theorem prime_sixtySixBL_10232267 : Nat.Prime 10232267 := by norm_num

private theorem prime_sixtySixBL_10279939 : Nat.Prime 10279939 := by norm_num

private theorem prime_sixtySixBL_10323583 : Nat.Prime 10323583 := by norm_num

private theorem prime_sixtySixBL_10727021 : Nat.Prime 10727021 := by norm_num

private theorem prime_sixtySixBL_10982483 : Nat.Prime 10982483 := by norm_num

private theorem prime_sixtySixBL_11678111 : Nat.Prime 11678111 := by norm_num

private theorem prime_sixtySixBL_11839237 : Nat.Prime 11839237 := by norm_num

private theorem prime_sixtySixBL_11940457 : Nat.Prime 11940457 := by norm_num

private theorem prime_sixtySixBL_12345017 : Nat.Prime 12345017 := by norm_num

private theorem prime_sixtySixBL_12541687 : Nat.Prime 12541687 := by norm_num

private theorem prime_sixtySixBL_12754033 : Nat.Prime 12754033 := by norm_num

private theorem prime_sixtySixBL_13013941 : Nat.Prime 13013941 := by norm_num

private theorem prime_sixtySixBL_13810721 : Nat.Prime 13810721 := by norm_num

private theorem prime_sixtySixBL_17425361 : Nat.Prime 17425361 := by norm_num

private theorem prime_sixtySixBL_20709473 : Nat.Prime 20709473 := by norm_num

private theorem prime_sixtySixBL_20875781 : Nat.Prime 20875781 := by norm_num

private theorem prime_sixtySixBL_21152011 : Nat.Prime 21152011 := by norm_num

private theorem prime_sixtySixBL_21958361 : Nat.Prime 21958361 := by norm_num

private theorem prime_sixtySixBL_22596253 : Nat.Prime 22596253 := by norm_num

private theorem prime_sixtySixBL_23366729 : Nat.Prime 23366729 := by norm_num

private theorem prime_sixtySixBL_23383849 : Nat.Prime 23383849 := by norm_num

private theorem prime_sixtySixBL_24947519 : Nat.Prime 24947519 := by norm_num

private theorem prime_sixtySixBL_26030933 : Nat.Prime 26030933 := by norm_num

private theorem prime_sixtySixBL_26080619 : Nat.Prime 26080619 := by norm_num

private theorem prime_sixtySixBL_28251907 : Nat.Prime 28251907 := by norm_num

private theorem prime_sixtySixBL_28488067 : Nat.Prime 28488067 := by norm_num

private theorem prime_sixtySixBL_29464571 : Nat.Prime 29464571 := by norm_num

private theorem prime_sixtySixBL_30057847 : Nat.Prime 30057847 := by
  apply lucas_primality 30057847 (5 : ZMod 30057847)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (55051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (55051, 1)] : List FactorBlock).map factorBlockValue).prod) = 30057847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_55051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30057847) ^ 15028923 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 30057847) ^ 10019282 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 30057847) ^ 4293978 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 30057847) ^ 2312142 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 30057847) ^ 546 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_30466529 : Nat.Prime 30466529 := by
  apply lucas_primality 30466529 (3 : ZMod 30466529)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 2), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 2), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 30466529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30466529) ^ 15233264 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 30466529) ^ 648224 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 30466529) ^ 70688 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_31429679 : Nat.Prime 31429679 := by
  apply lucas_primality 31429679 (7 : ZMod 31429679)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (29, 1), (11059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (29, 1), (11059, 1)] : List FactorBlock).map factorBlockValue).prod) = 31429679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_11059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31429679) ^ 15714839 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 31429679) ^ 4489954 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 31429679) ^ 1083782 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 31429679) ^ 2842 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_32388127 : Nat.Prime 32388127 := by
  apply lucas_primality 32388127 (3 : ZMod 32388127)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2069, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2069, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) = 32388127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_2069
      · exact prime_sixtySixBL_2609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32388127) ^ 16194063 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 32388127) ^ 10796042 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 32388127) ^ 15654 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 32388127) ^ 12414 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_33784061 : Nat.Prime 33784061 := by
  apply lucas_primality 33784061 (3 : ZMod 33784061)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (379, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (379, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) = 33784061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_379
      · exact prime_sixtySixBL_4457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33784061) ^ 16892030 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33784061) ^ 6756812 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33784061) ^ 89140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33784061) ^ 7580 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_35557273 : Nat.Prime 35557273 := by
  apply lucas_primality 35557273 (7 : ZMod 35557273)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (164617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (164617, 1)] : List FactorBlock).map factorBlockValue).prod) = 35557273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_164617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 35557273) ^ 17778636 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 35557273) ^ 11852424 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 35557273) ^ 216 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_38534009 : Nat.Prime 38534009 := by
  apply lucas_primality 38534009 (3 : ZMod 38534009)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4816751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4816751, 1)] : List FactorBlock).map factorBlockValue).prod) = 38534009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_4816751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 38534009) ^ 19267004 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 38534009) ^ 8 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_39134111 : Nat.Prime 39134111 := by
  apply lucas_primality 39134111 (11 : ZMod 39134111)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (59, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (59, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) = 39134111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_59
      · exact prime_sixtySixBL_3491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39134111) ^ 19567055 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 39134111) ^ 7826822 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 39134111) ^ 2059690 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 39134111) ^ 663290 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 39134111) ^ 11210 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_41331139 : Nat.Prime 41331139 := by
  apply lucas_primality 41331139 (2 : ZMod 41331139)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (299501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (299501, 1)] : List FactorBlock).map factorBlockValue).prod) = 41331139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_299501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41331139) ^ 20665569 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41331139) ^ 13777046 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41331139) ^ 1797006 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41331139) ^ 138 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_42367687 : Nat.Prime 42367687 := by
  apply lucas_primality 42367687 (5 : ZMod 42367687)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7061281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7061281, 1)] : List FactorBlock).map factorBlockValue).prod) = 42367687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7061281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42367687) ^ 21183843 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 42367687) ^ 14122562 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 42367687) ^ 6 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_43774391 : Nat.Prime 43774391 := by
  apply lucas_primality 43774391 (17 : ZMod 43774391)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (47, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (47, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) = 43774391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_8467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 43774391) ^ 21887195 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 43774391) ^ 8754878 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 43774391) ^ 3979490 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 43774391) ^ 931370 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 43774391) ^ 5170 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_43916723 : Nat.Prime 43916723 := by
  apply lucas_primality 43916723 (2 : ZMod 43916723)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21958361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21958361, 1)] : List FactorBlock).map factorBlockValue).prod) = 43916723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_21958361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 43916723) ^ 21958361 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916723) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_46573531 : Nat.Prime 46573531 := by
  apply lucas_primality 46573531 (2 : ZMod 46573531)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1552451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1552451, 1)] : List FactorBlock).map factorBlockValue).prod) = 46573531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_1552451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46573531) ^ 23286765 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 46573531) ^ 15524510 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 46573531) ^ 9314706 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 46573531) ^ 30 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_49912237 : Nat.Prime 49912237 := by
  apply lucas_primality 49912237 (2 : ZMod 49912237)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (126041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (126041, 1)] : List FactorBlock).map factorBlockValue).prod) = 49912237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_126041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49912237) ^ 24956118 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49912237) ^ 16637412 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49912237) ^ 4537476 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49912237) ^ 396 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_51494461 : Nat.Prime 51494461 := by
  apply lucas_primality 51494461 (2 : ZMod 51494461)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (858241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (858241, 1)] : List FactorBlock).map factorBlockValue).prod) = 51494461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_858241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51494461) ^ 25747230 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 51494461) ^ 17164820 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 51494461) ^ 10298892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 51494461) ^ 60 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_52147201 : Nat.Prime 52147201 := by
  apply lucas_primality 52147201 (22 : ZMod 52147201)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (5, 2), (7, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (5, 2), (7, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 52147201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 52147201) ^ 26073600 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (22 : ZMod 52147201) ^ 17382400 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (22 : ZMod 52147201) ^ 10429440 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (22 : ZMod 52147201) ^ 7449600 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (22 : ZMod 52147201) ^ 537600 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_55453469 : Nat.Prime 55453469 := by
  apply lucas_primality 55453469 (2 : ZMod 55453469)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (829, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (829, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 55453469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_829
      · exact prime_sixtySixBL_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55453469) ^ 27726734 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55453469) ^ 7921924 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55453469) ^ 66892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55453469) ^ 23212 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_57529987 : Nat.Prime 57529987 := by
  apply lucas_primality 57529987 (2 : ZMod 57529987)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (73, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (73, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 57529987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57529987) ^ 28764993 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57529987) ^ 19176662 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57529987) ^ 3027894 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57529987) ^ 1855806 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57529987) ^ 788082 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57529987) ^ 257982 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_62794013 : Nat.Prime 62794013 := by
  apply lucas_primality 62794013 (2 : ZMod 62794013)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (571, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (571, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 62794013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_571
      · exact prime_sixtySixBL_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62794013) ^ 31397006 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 62794013) ^ 3304948 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 62794013) ^ 109972 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 62794013) ^ 43396 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_66678137 : Nat.Prime 66678137 := by
  apply lucas_primality 66678137 (3 : ZMod 66678137)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41, 1), (113, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41, 1), (113, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 66678137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_113
      · exact prime_sixtySixBL_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66678137) ^ 33339068 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 66678137) ^ 9525448 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 66678137) ^ 1626296 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 66678137) ^ 590072 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 66678137) ^ 259448 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_69536491 : Nat.Prime 69536491 := by
  apply lucas_primality 69536491 (2 : ZMod 69536491)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (257, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (257, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 69536491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_257
      · exact prime_sixtySixBL_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69536491) ^ 34768245 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69536491) ^ 23178830 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69536491) ^ 13907298 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69536491) ^ 2397810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69536491) ^ 270570 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69536491) ^ 223590 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_71397707 : Nat.Prime 71397707 := by
  apply lucas_primality 71397707 (2 : ZMod 71397707)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1878887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1878887, 1)] : List FactorBlock).map factorBlockValue).prod) = 71397707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_1878887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71397707) ^ 35698853 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 71397707) ^ 3757774 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 71397707) ^ 38 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_75560783 : Nat.Prime 75560783 := by
  apply lucas_primality 75560783 (5 : ZMod 75560783)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3434581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3434581, 1)] : List FactorBlock).map factorBlockValue).prod) = 75560783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_3434581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 75560783) ^ 37780391 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75560783) ^ 6869162 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75560783) ^ 22 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_98065087 : Nat.Prime 98065087 := by
  apply lucas_primality 98065087 (3 : ZMod 98065087)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (67, 1), (34849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (67, 1), (34849, 1)] : List FactorBlock).map factorBlockValue).prod) = 98065087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_34849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 98065087) ^ 49032543 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98065087) ^ 32688362 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98065087) ^ 14009298 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98065087) ^ 1463658 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 98065087) ^ 2814 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_100456303 : Nat.Prime 100456303 := by
  apply lucas_primality 100456303 (3 : ZMod 100456303)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (127807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (127807, 1)] : List FactorBlock).map factorBlockValue).prod) = 100456303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_131
      · exact prime_sixtySixBL_127807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 100456303) ^ 50228151 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 100456303) ^ 33485434 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 100456303) ^ 766842 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 100456303) ^ 786 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_103547267 : Nat.Prime 103547267 := by
  apply lucas_primality 103547267 (2 : ZMod 103547267)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (577, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (577, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 103547267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_577
      · exact prime_sixtySixBL_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103547267) ^ 51773633 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 103547267) ^ 1953722 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 103547267) ^ 179458 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 103547267) ^ 61162 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_106475701 : Nat.Prime 106475701 := by
  apply lucas_primality 106475701 (2 : ZMod 106475701)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (31, 1), (107, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (31, 1), (107, 2)] : List FactorBlock).map factorBlockValue).prod) = 106475701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106475701) ^ 53237850 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 106475701) ^ 35491900 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 106475701) ^ 21295140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 106475701) ^ 3434700 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 106475701) ^ 995100 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_117455419 : Nat.Prime 117455419 := by
  apply lucas_primality 117455419 (2 : ZMod 117455419)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6525301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6525301, 1)] : List FactorBlock).map factorBlockValue).prod) = 117455419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_6525301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 117455419) ^ 58727709 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117455419) ^ 39151806 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117455419) ^ 18 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_120187999 : Nat.Prime 120187999 := by
  apply lucas_primality 120187999 (7 : ZMod 120187999)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (953873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (953873, 1)] : List FactorBlock).map factorBlockValue).prod) = 120187999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_953873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 120187999) ^ 60093999 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 120187999) ^ 40062666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 120187999) ^ 17169714 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 120187999) ^ 126 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_129552509 : Nat.Prime 129552509 := by
  apply lucas_primality 129552509 (2 : ZMod 129552509)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (32388127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (32388127, 1)] : List FactorBlock).map factorBlockValue).prod) = 129552509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_32388127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 129552509) ^ 64776254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 129552509) ^ 4 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_154682441 : Nat.Prime 154682441 := by
  apply lucas_primality 154682441 (6 : ZMod 154682441)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (351551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (351551, 1)] : List FactorBlock).map factorBlockValue).prod) = 154682441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_351551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 154682441) ^ 77341220 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 154682441) ^ 30936488 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 154682441) ^ 14062040 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 154682441) ^ 440 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_197181073 : Nat.Prime 197181073 := by
  apply lucas_primality 197181073 (5 : ZMod 197181073)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (281, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (281, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 197181073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_281
      · exact prime_sixtySixBL_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 197181073) ^ 98590536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 197181073) ^ 65727024 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 197181073) ^ 17925552 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 197181073) ^ 701712 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 197181073) ^ 445104 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_208467817 : Nat.Prime 208467817 := by
  apply lucas_primality 208467817 (5 : ZMod 208467817)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8686159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8686159, 1)] : List FactorBlock).map factorBlockValue).prod) = 208467817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_8686159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 208467817) ^ 104233908 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 208467817) ^ 69489272 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 208467817) ^ 24 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_235760431 : Nat.Prime 235760431 := by
  apply lucas_primality 235760431 (3 : ZMod 235760431)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (53, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (53, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) = 235760431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_5113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 235760431) ^ 117880215 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 235760431) ^ 78586810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 235760431) ^ 47152086 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 235760431) ^ 8129670 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 235760431) ^ 4448310 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 235760431) ^ 46110 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_237168809 : Nat.Prime 237168809 := by
  apply lucas_primality 237168809 (3 : ZMod 237168809)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4729, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4729, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 237168809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_4729
      · exact prime_sixtySixBL_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 237168809) ^ 118584404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 237168809) ^ 50152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 237168809) ^ 37832 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_250581421 : Nat.Prime 250581421 := by
  apply lucas_primality 250581421 (2 : ZMod 250581421)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (157, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (157, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) = 250581421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_157
      · exact prime_sixtySixBL_8867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 250581421) ^ 125290710 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 250581421) ^ 83527140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 250581421) ^ 50116284 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 250581421) ^ 1596060 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 250581421) ^ 28260 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_251606941 : Nat.Prime 251606941 := by
  apply lucas_primality 251606941 (2 : ZMod 251606941)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (322573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (322573, 1)] : List FactorBlock).map factorBlockValue).prod) = 251606941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_322573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251606941) ^ 125803470 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 251606941) ^ 83868980 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 251606941) ^ 50321388 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 251606941) ^ 19354380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 251606941) ^ 780 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_282897899 : Nat.Prime 282897899 := by
  apply lucas_primality 282897899 (2 : ZMod 282897899)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (617681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (617681, 1)] : List FactorBlock).map factorBlockValue).prod) = 282897899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_229
      · exact prime_sixtySixBL_617681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 282897899) ^ 141448949 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282897899) ^ 1235362 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 282897899) ^ 458 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_284085911 : Nat.Prime 284085911 := by
  apply lucas_primality 284085911 (7 : ZMod 284085911)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (71, 1), (21059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (71, 1), (21059, 1)] : List FactorBlock).map factorBlockValue).prod) = 284085911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_71
      · exact prime_sixtySixBL_21059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 284085911) ^ 142042955 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 284085911) ^ 56817182 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 284085911) ^ 14951890 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 284085911) ^ 4001210 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 284085911) ^ 13490 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_285147727 : Nat.Prime 285147727 := by
  apply lucas_primality 285147727 (3 : ZMod 285147727)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1181, 1), (40241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1181, 1), (40241, 1)] : List FactorBlock).map factorBlockValue).prod) = 285147727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1181
      · exact prime_sixtySixBL_40241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 285147727) ^ 142573863 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 285147727) ^ 95049242 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 285147727) ^ 241446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 285147727) ^ 7086 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_317855033 : Nat.Prime 317855033 := by
  apply lucas_primality 317855033 (3 : ZMod 317855033)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (23, 1), (97, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (23, 1), (97, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 317855033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 317855033) ^ 158927516 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 317855033) ^ 28895912 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 317855033) ^ 13819784 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 317855033) ^ 3276856 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 317855033) ^ 196328 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_419637121 : Nat.Prime 419637121 := by
  apply lucas_primality 419637121 (11 : ZMod 419637121)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (7, 1), (31223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (7, 1), (31223, 1)] : List FactorBlock).map factorBlockValue).prod) = 419637121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_31223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 419637121) ^ 209818560 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 419637121) ^ 139879040 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 419637121) ^ 83927424 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 419637121) ^ 59948160 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 419637121) ^ 13440 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_435844723 : Nat.Prime 435844723 := by
  apply lucas_primality 435844723 (2 : ZMod 435844723)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (445649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (445649, 1)] : List FactorBlock).map factorBlockValue).prod) = 435844723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_163
      · exact prime_sixtySixBL_445649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 435844723) ^ 217922361 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 435844723) ^ 145281574 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 435844723) ^ 2673894 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 435844723) ^ 978 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_484220999 : Nat.Prime 484220999 := by
  apply lucas_primality 484220999 (11 : ZMod 484220999)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (503, 1), (13009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (503, 1), (13009, 1)] : List FactorBlock).map factorBlockValue).prod) = 484220999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_37
      · exact prime_sixtySixBL_503
      · exact prime_sixtySixBL_13009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 484220999) ^ 242110499 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 484220999) ^ 13087054 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 484220999) ^ 962666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 484220999) ^ 37222 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_506676977 : Nat.Prime 506676977 := by
  apply lucas_primality 506676977 (3 : ZMod 506676977)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 1), (143291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 1), (143291, 1)] : List FactorBlock).map factorBlockValue).prod) = 506676977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_143291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 506676977) ^ 253338488 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 506676977) ^ 38975152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 506676977) ^ 29804528 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 506676977) ^ 3536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_560549329 : Nat.Prime 560549329 := by
  apply lucas_primality 560549329 (11 : ZMod 560549329)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11678111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11678111, 1)] : List FactorBlock).map factorBlockValue).prod) = 560549329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11678111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 560549329) ^ 280274664 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 560549329) ^ 186849776 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 560549329) ^ 48 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_635710067 : Nat.Prime 635710067 := by
  apply lucas_primality 635710067 (2 : ZMod 635710067)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317855033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317855033, 1)] : List FactorBlock).map factorBlockValue).prod) = 635710067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_317855033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 635710067) ^ 317855033 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 635710067) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_639056263 : Nat.Prime 639056263 := by
  apply lucas_primality 639056263 (5 : ZMod 639056263)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (199, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (199, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) = 639056263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_199
      · exact prime_sixtySixBL_3167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 639056263) ^ 319528131 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 639056263) ^ 213018754 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 639056263) ^ 49158174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 639056263) ^ 3211338 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 639056263) ^ 201786 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_655564213 : Nat.Prime 655564213 := by
  apply lucas_primality 655564213 (2 : ZMod 655564213)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (83, 1), (73133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (83, 1), (73133, 1)] : List FactorBlock).map factorBlockValue).prod) = 655564213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_83
      · exact prime_sixtySixBL_73133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 655564213) ^ 327782106 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 655564213) ^ 218521404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 655564213) ^ 7898364 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 655564213) ^ 8964 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_781883731 : Nat.Prime 781883731 := by
  apply lucas_primality 781883731 (3 : ZMod 781883731)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (659, 1), (13183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (659, 1), (13183, 1)] : List FactorBlock).map factorBlockValue).prod) = 781883731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_659
      · exact prime_sixtySixBL_13183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 781883731) ^ 390941865 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 781883731) ^ 260627910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 781883731) ^ 156376746 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 781883731) ^ 1186470 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 781883731) ^ 59310 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_790567073 : Nat.Prime 790567073 := by
  apply lucas_primality 790567073 (3 : ZMod 790567073)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 1), (97, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 1), (97, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) = 790567073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_5419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 790567073) ^ 395283536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 790567073) ^ 16820576 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 790567073) ^ 8150176 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 790567073) ^ 145888 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_827407699 : Nat.Prime 827407699 := by
  apply lucas_primality 827407699 (14 : ZMod 827407699)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (233, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (233, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 827407699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_233
      · exact prime_sixtySixBL_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 827407699) ^ 413703849 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 827407699) ^ 275802566 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 827407699) ^ 63646746 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 827407699) ^ 15611466 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 827407699) ^ 3551106 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 827407699) ^ 963222 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_932124419 : Nat.Prime 932124419 := by
  apply lucas_primality 932124419 (2 : ZMod 932124419)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12347, 1), (37747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12347, 1), (37747, 1)] : List FactorBlock).map factorBlockValue).prod) = 932124419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_12347
      · exact prime_sixtySixBL_37747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 932124419) ^ 466062209 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 932124419) ^ 75494 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 932124419) ^ 24694 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1004729927 : Nat.Prime 1004729927 := by
  apply lucas_primality 1004729927 (5 : ZMod 1004729927)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18701, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18701, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1004729927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_18701
      · exact prime_sixtySixBL_26863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1004729927) ^ 502364963 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004729927) ^ 53726 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1004729927) ^ 37402 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1202313881 : Nat.Prime 1202313881 := by
  apply lucas_primality 1202313881 (7 : ZMod 1202313881)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (30057847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (30057847, 1)] : List FactorBlock).map factorBlockValue).prod) = 1202313881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_30057847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1202313881) ^ 601156940 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1202313881) ^ 240462776 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1202313881) ^ 40 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1279594219 : Nat.Prime 1279594219 := by
  apply lucas_primality 1279594219 (2 : ZMod 1279594219)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (30466529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (30466529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1279594219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_30466529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1279594219) ^ 639797109 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1279594219) ^ 426531406 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1279594219) ^ 182799174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1279594219) ^ 42 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1383273691 : Nat.Prime 1383273691 := by
  apply lucas_primality 1383273691 (3 : ZMod 1383273691)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2857, 1), (16139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2857, 1), (16139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1383273691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_2857
      · exact prime_sixtySixBL_16139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1383273691) ^ 691636845 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383273691) ^ 461091230 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383273691) ^ 276654738 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383273691) ^ 484170 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1383273691) ^ 85710 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1493910983 : Nat.Prime 1493910983 := by
  apply lucas_primality 1493910983 (5 : ZMod 1493910983)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (10232267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (10232267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1493910983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_10232267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1493910983) ^ 746955491 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1493910983) ^ 20464534 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1493910983) ^ 146 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1581002029 : Nat.Prime 1581002029 := by
  apply lucas_primality 1581002029 (2 : ZMod 1581002029)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43916723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43916723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581002029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_43916723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1581002029) ^ 790501014 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581002029) ^ 527000676 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581002029) ^ 36 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1818338149 : Nat.Prime 1818338149 := by
  apply lucas_primality 1818338149 (2 : ZMod 1818338149)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (101, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (101, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1818338149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_101
      · exact prime_sixtySixBL_4133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1818338149) ^ 909169074 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818338149) ^ 606112716 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818338149) ^ 165303468 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818338149) ^ 18003348 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1818338149) ^ 439956 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1970829121 : Nat.Prime 1970829121 := by
  apply lucas_primality 1970829121 (11 : ZMod 1970829121)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (13, 1), (67, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (13, 1), (67, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1970829121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_2357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1970829121) ^ 985414560 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1970829121) ^ 656943040 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1970829121) ^ 394165824 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1970829121) ^ 151602240 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1970829121) ^ 29415360 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1970829121) ^ 836160 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2091491951 : Nat.Prime 2091491951 := by
  apply lucas_primality 2091491951 (17 : ZMod 2091491951)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1181, 1), (35419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1181, 1), (35419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091491951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_1181
      · exact prime_sixtySixBL_35419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2091491951) ^ 1045745975 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 2091491951) ^ 418298390 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 2091491951) ^ 1770950 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 2091491951) ^ 59050 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2126520287 : Nat.Prime 2126520287 := by
  apply lucas_primality 2126520287 (5 : ZMod 2126520287)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (257, 1), (569, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (257, 1), (569, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2126520287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_257
      · exact prime_sixtySixBL_569
      · exact prime_sixtySixBL_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2126520287) ^ 1063260143 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2126520287) ^ 193320026 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2126520287) ^ 8274398 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2126520287) ^ 3737294 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2126520287) ^ 3217126 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2242197317 : Nat.Prime 2242197317 := by
  apply lucas_primality 2242197317 (2 : ZMod 2242197317)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (560549329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (560549329, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242197317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_560549329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2242197317) ^ 1121098658 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2242197317) ^ 4 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2354867329 : Nat.Prime 2354867329 := by
  apply lucas_primality 2354867329 (19 : ZMod 2354867329)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (11, 1), (23, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (11, 1), (23, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2354867329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_24239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2354867329) ^ 1177433664 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (19 : ZMod 2354867329) ^ 784955776 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (19 : ZMod 2354867329) ^ 214078848 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (19 : ZMod 2354867329) ^ 102385536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (19 : ZMod 2354867329) ^ 97152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2922598051 : Nat.Prime 2922598051 := by
  apply lucas_primality 2922598051 (2 : ZMod 2922598051)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (19, 1), (829, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (19, 1), (829, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2922598051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_829
      · exact prime_sixtySixBL_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2922598051) ^ 1461299025 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2922598051) ^ 974199350 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2922598051) ^ 584519610 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2922598051) ^ 153820950 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2922598051) ^ 3525450 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2922598051) ^ 2362650 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3064646561 : Nat.Prime 3064646561 := by
  apply lucas_primality 3064646561 (3 : ZMod 3064646561)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (53, 1), (173, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (53, 1), (173, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) = 3064646561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_173
      · exact prime_sixtySixBL_2089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3064646561) ^ 1532323280 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3064646561) ^ 612929312 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3064646561) ^ 57823520 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3064646561) ^ 17714720 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3064646561) ^ 1467040 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3087678889 : Nat.Prime 3087678889 := by
  apply lucas_primality 3087678889 (23 : ZMod 3087678889)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (6126347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (6126347, 1)] : List FactorBlock).map factorBlockValue).prod) = 3087678889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_6126347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 3087678889) ^ 1543839444 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (23 : ZMod 3087678889) ^ 1029226296 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (23 : ZMod 3087678889) ^ 441096984 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (23 : ZMod 3087678889) ^ 504 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3092188733 : Nat.Prime 3092188733 := by
  apply lucas_primality 3092188733 (2 : ZMod 3092188733)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (2518069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (2518069, 1)] : List FactorBlock).map factorBlockValue).prod) = 3092188733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_307
      · exact prime_sixtySixBL_2518069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3092188733) ^ 1546094366 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3092188733) ^ 10072276 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3092188733) ^ 1228 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3463574321 : Nat.Prime 3463574321 := by
  apply lucas_primality 3463574321 (6 : ZMod 3463574321)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (43, 1), (1006853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (43, 1), (1006853, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463574321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_43
      · exact prime_sixtySixBL_1006853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3463574321) ^ 1731787160 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463574321) ^ 692714864 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463574321) ^ 80548240 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3463574321) ^ 3440 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3816321581 : Nat.Prime 3816321581 := by
  apply lucas_primality 3816321581 (2 : ZMod 3816321581)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1231, 1), (155009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1231, 1), (155009, 1)] : List FactorBlock).map factorBlockValue).prod) = 3816321581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_1231
      · exact prime_sixtySixBL_155009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3816321581) ^ 1908160790 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816321581) ^ 763264316 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816321581) ^ 3100180 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816321581) ^ 24620 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4057168579 : Nat.Prime 4057168579 := by
  apply lucas_primality 4057168579 (2 : ZMod 4057168579)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2689, 1), (251467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2689, 1), (251467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4057168579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_2689
      · exact prime_sixtySixBL_251467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4057168579) ^ 2028584289 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4057168579) ^ 1352389526 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4057168579) ^ 1508802 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4057168579) ^ 16134 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4083843047 : Nat.Prime 4083843047 := by
  apply lucas_primality 4083843047 (5 : ZMod 4083843047)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (227, 1), (310181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (227, 1), (310181, 1)] : List FactorBlock).map factorBlockValue).prod) = 4083843047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_227
      · exact prime_sixtySixBL_310181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4083843047) ^ 2041921523 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4083843047) ^ 140822174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4083843047) ^ 17990498 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4083843047) ^ 13166 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4496453579 : Nat.Prime 4496453579 := by
  apply lucas_primality 4496453579 (2 : ZMod 4496453579)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12577, 1), (178757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12577, 1), (178757, 1)] : List FactorBlock).map factorBlockValue).prod) = 4496453579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_12577
      · exact prime_sixtySixBL_178757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4496453579) ^ 2248226789 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4496453579) ^ 357514 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4496453579) ^ 25154 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5372252141 : Nat.Prime 5372252141 := by
  apply lucas_primality 5372252141 (2 : ZMod 5372252141)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (41, 1), (443, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (41, 1), (443, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 5372252141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_443
      · exact prime_sixtySixBL_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5372252141) ^ 2686126070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5372252141) ^ 1074450428 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5372252141) ^ 233576180 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5372252141) ^ 131030540 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5372252141) ^ 12126980 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5372252141) ^ 8354980 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_6951088349 : Nat.Prime 6951088349 := by
  apply lucas_primality 6951088349 (2 : ZMod 6951088349)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (28488067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (28488067, 1)] : List FactorBlock).map factorBlockValue).prod) = 6951088349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_61
      · exact prime_sixtySixBL_28488067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6951088349) ^ 3475544174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6951088349) ^ 113952268 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6951088349) ^ 244 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7504841413 : Nat.Prime 7504841413 := by
  apply lucas_primality 7504841413 (2 : ZMod 7504841413)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (208467817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (208467817, 1)] : List FactorBlock).map factorBlockValue).prod) = 7504841413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_208467817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7504841413) ^ 3752420706 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7504841413) ^ 2501613804 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7504841413) ^ 36 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7632643163 : Nat.Prime 7632643163 := by
  apply lucas_primality 7632643163 (2 : ZMod 7632643163)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3816321581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3816321581, 1)] : List FactorBlock).map factorBlockValue).prod) = 7632643163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3816321581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7632643163) ^ 3816321581 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7632643163) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_9120185587 : Nat.Prime 9120185587 := by
  apply lucas_primality 9120185587 (5 : ZMod 9120185587)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (506676977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (506676977, 1)] : List FactorBlock).map factorBlockValue).prod) = 9120185587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_506676977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9120185587) ^ 4560092793 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9120185587) ^ 3040061862 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9120185587) ^ 18 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_9194386753 : Nat.Prime 9194386753 := by
  apply lucas_primality 9194386753 (5 : ZMod 9194386753)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (83, 1), (192319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (83, 1), (192319, 1)] : List FactorBlock).map factorBlockValue).prod) = 9194386753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_83
      · exact prime_sixtySixBL_192319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9194386753) ^ 4597193376 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9194386753) ^ 3064795584 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9194386753) ^ 110775744 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9194386753) ^ 47808 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_10242543593 : Nat.Prime 10242543593 := by
  apply lucas_primality 10242543593 (3 : ZMod 10242543593)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (5471, 1), (7549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (5471, 1), (7549, 1)] : List FactorBlock).map factorBlockValue).prod) = 10242543593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_5471
      · exact prime_sixtySixBL_7549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10242543593) ^ 5121271796 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10242543593) ^ 330404632 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10242543593) ^ 1872152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 10242543593) ^ 1356808 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_11185493029 : Nat.Prime 11185493029 := by
  apply lucas_primality 11185493029 (2 : ZMod 11185493029)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (932124419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (932124419, 1)] : List FactorBlock).map factorBlockValue).prod) = 11185493029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_932124419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11185493029) ^ 5592746514 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11185493029) ^ 3728497676 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11185493029) ^ 12 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_11320314871 : Nat.Prime 11320314871 := by
  apply lucas_primality 11320314871 (3 : ZMod 11320314871)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (8641, 1), (43669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (8641, 1), (43669, 1)] : List FactorBlock).map factorBlockValue).prod) = 11320314871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_8641
      · exact prime_sixtySixBL_43669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11320314871) ^ 5660157435 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11320314871) ^ 3773438290 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11320314871) ^ 2264062974 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11320314871) ^ 1310070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11320314871) ^ 259230 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_13595769641 : Nat.Prime 13595769641 := by
  apply lucas_primality 13595769641 (3 : ZMod 13595769641)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (191, 1), (349, 1), (5099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (191, 1), (349, 1), (5099, 1)] : List FactorBlock).map factorBlockValue).prod) = 13595769641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_191
      · exact prime_sixtySixBL_349
      · exact prime_sixtySixBL_5099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13595769641) ^ 6797884820 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13595769641) ^ 2719153928 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13595769641) ^ 71182040 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13595769641) ^ 38956360 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 13595769641) ^ 2666360 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_14320270193 : Nat.Prime 14320270193 := by
  apply lucas_primality 14320270193 (3 : ZMod 14320270193)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (2477, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (2477, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) = 14320270193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_2477
      · exact prime_sixtySixBL_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14320270193) ^ 7160135096 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320270193) ^ 213735376 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320270193) ^ 5781296 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14320270193) ^ 2655344 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_15982992863 : Nat.Prime 15982992863 := by
  apply lucas_primality 15982992863 (5 : ZMod 15982992863)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (26030933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (26030933, 1)] : List FactorBlock).map factorBlockValue).prod) = 15982992863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_307
      · exact prime_sixtySixBL_26030933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15982992863) ^ 7991496431 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 15982992863) ^ 52061866 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 15982992863) ^ 614 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_16471038211 : Nat.Prime 16471038211 := by
  apply lucas_primality 16471038211 (3 : ZMod 16471038211)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (49912237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (49912237, 1)] : List FactorBlock).map factorBlockValue).prod) = 16471038211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_49912237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16471038211) ^ 8235519105 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16471038211) ^ 5490346070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16471038211) ^ 3294207642 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16471038211) ^ 1497367110 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 16471038211) ^ 330 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_16872683963 : Nat.Prime 16872683963 := by
  apply lucas_primality 16872683963 (2 : ZMod 16872683963)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (5620481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (5620481, 1)] : List FactorBlock).map factorBlockValue).prod) = 16872683963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_79
      · exact prime_sixtySixBL_5620481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16872683963) ^ 8436341981 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 16872683963) ^ 888035998 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 16872683963) ^ 213578278 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 16872683963) ^ 3002 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_17489116049 : Nat.Prime 17489116049 := by
  apply lucas_primality 17489116049 (3 : ZMod 17489116049)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (57529987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (57529987, 1)] : List FactorBlock).map factorBlockValue).prod) = 17489116049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_57529987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17489116049) ^ 8744558024 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17489116049) ^ 920479792 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 17489116049) ^ 304 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_17717173013 : Nat.Prime 17717173013 := by
  apply lucas_primality 17717173013 (2 : ZMod 17717173013)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (59, 1), (974971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (59, 1), (974971, 1)] : List FactorBlock).map factorBlockValue).prod) = 17717173013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_59
      · exact prime_sixtySixBL_974971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17717173013) ^ 8858586506 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717173013) ^ 2531024716 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717173013) ^ 1610652092 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717173013) ^ 300291068 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717173013) ^ 18172 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_19644809269 : Nat.Prime 19644809269 := by
  apply lucas_primality 19644809269 (10 : ZMod 19644809269)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (197, 1), (1187141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (197, 1), (1187141, 1)] : List FactorBlock).map factorBlockValue).prod) = 19644809269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_197
      · exact prime_sixtySixBL_1187141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19644809269) ^ 9822404634 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19644809269) ^ 6548269756 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19644809269) ^ 2806401324 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19644809269) ^ 99719844 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19644809269) ^ 16548 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_19676372977 : Nat.Prime 19676372977 := by
  apply lucas_primality 19676372977 (10 : ZMod 19676372977)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (41, 1), (256363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (41, 1), (256363, 1)] : List FactorBlock).map factorBlockValue).prod) = 19676372977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_256363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19676372977) ^ 9838186488 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19676372977) ^ 6558790992 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19676372977) ^ 1513567152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19676372977) ^ 479911536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 19676372977) ^ 76752 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_28640540387 : Nat.Prime 28640540387 := by
  apply lucas_primality 28640540387 (2 : ZMod 28640540387)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14320270193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14320270193, 1)] : List FactorBlock).map factorBlockValue).prod) = 28640540387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_14320270193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28640540387) ^ 14320270193 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 28640540387) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_37330035137 : Nat.Prime 37330035137 := by
  apply lucas_primality 37330035137 (3 : ZMod 37330035137)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (43, 1), (577, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (43, 1), (577, 1), (23509, 1)] : List FactorBlock).map factorBlockValue).prod) = 37330035137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_43
      · exact prime_sixtySixBL_577
      · exact prime_sixtySixBL_23509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37330035137) ^ 18665017568 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 37330035137) ^ 868140352 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 37330035137) ^ 64696768 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 37330035137) ^ 1587904 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_37611336491 : Nat.Prime 37611336491 := by
  apply lucas_primality 37611336491 (2 : ZMod 37611336491)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (41331139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (41331139, 1)] : List FactorBlock).map factorBlockValue).prod) = 37611336491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_41331139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37611336491) ^ 18805668245 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37611336491) ^ 7522267298 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37611336491) ^ 5373048070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37611336491) ^ 2893179730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 37611336491) ^ 910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_39599431213 : Nat.Prime 39599431213 := by
  apply lucas_primality 39599431213 (2 : ZMod 39599431213)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (1759, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (1759, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 39599431213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_1759
      · exact prime_sixtySixBL_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39599431213) ^ 19799715606 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39599431213) ^ 13199810404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39599431213) ^ 3599948292 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39599431213) ^ 1365497628 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39599431213) ^ 22512468 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39599431213) ^ 6733452 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_42181629643 : Nat.Prime 42181629643 := by
  apply lucas_primality 42181629643 (2 : ZMod 42181629643)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (853, 1), (2747273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (853, 1), (2747273, 1)] : List FactorBlock).map factorBlockValue).prod) = 42181629643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_853
      · exact prime_sixtySixBL_2747273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42181629643) ^ 21090814821 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 42181629643) ^ 14060543214 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 42181629643) ^ 49450914 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 42181629643) ^ 15354 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_48250020127 : Nat.Prime 48250020127 := by
  apply lucas_primality 48250020127 (3 : ZMod 48250020127)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (37, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (37, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) = 48250020127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_37
      · exact prime_sixtySixBL_7219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48250020127) ^ 24125010063 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 16083340042 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 6892860018 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 4386365466 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 2838236478 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 2097826962 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 1304054598 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 48250020127) ^ 6683754 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_48386354893 : Nat.Prime 48386354893 := by
  apply lucas_primality 48386354893 (2 : ZMod 48386354893)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4111, 1), (980831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4111, 1), (980831, 1)] : List FactorBlock).map factorBlockValue).prod) = 48386354893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_4111
      · exact prime_sixtySixBL_980831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48386354893) ^ 24193177446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 48386354893) ^ 16128784964 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 48386354893) ^ 11769972 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 48386354893) ^ 49332 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_60915790241 : Nat.Prime 60915790241 := by
  apply lucas_primality 60915790241 (3 : ZMod 60915790241)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (73, 1), (5215393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (73, 1), (5215393, 1)] : List FactorBlock).map factorBlockValue).prod) = 60915790241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_5215393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60915790241) ^ 30457895120 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 60915790241) ^ 12183158048 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 60915790241) ^ 834462880 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 60915790241) ^ 11680 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_63844349731 : Nat.Prime 63844349731 := by
  apply lucas_primality 63844349731 (2 : ZMod 63844349731)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (4339, 1), (70067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (4339, 1), (70067, 1)] : List FactorBlock).map factorBlockValue).prod) = 63844349731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_4339
      · exact prime_sixtySixBL_70067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63844349731) ^ 31922174865 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63844349731) ^ 21281449910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63844349731) ^ 12768869946 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63844349731) ^ 9120621390 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63844349731) ^ 14714070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 63844349731) ^ 911190 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_69073414301 : Nat.Prime 69073414301 := by
  apply lucas_primality 69073414301 (2 : ZMod 69073414301)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (62794013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (62794013, 1)] : List FactorBlock).map factorBlockValue).prod) = 69073414301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_62794013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69073414301) ^ 34536707150 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69073414301) ^ 13814682860 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69073414301) ^ 6279401300 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 69073414301) ^ 1100 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_75222672983 : Nat.Prime 75222672983 := by
  apply lucas_primality 75222672983 (5 : ZMod 75222672983)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37611336491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37611336491, 1)] : List FactorBlock).map factorBlockValue).prod) = 75222672983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_37611336491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 75222672983) ^ 37611336491 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75222672983) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_75715110761 : Nat.Prime 75715110761 := by
  apply lucas_primality 75715110761 (3 : ZMod 75715110761)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (67, 1), (28251907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (67, 1), (28251907, 1)] : List FactorBlock).map factorBlockValue).prod) = 75715110761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_28251907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75715110761) ^ 37857555380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75715110761) ^ 15143022152 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75715110761) ^ 1130076280 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 75715110761) ^ 2680 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_110903758513 : Nat.Prime 110903758513 := by
  apply lucas_primality 110903758513 (5 : ZMod 110903758513)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (100456303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (100456303, 1)] : List FactorBlock).map factorBlockValue).prod) = 110903758513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_100456303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 110903758513) ^ 55451879256 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 110903758513) ^ 36967919504 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 110903758513) ^ 4821902544 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 110903758513) ^ 1104 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_117389043397 : Nat.Prime 117389043397 := by
  apply lucas_primality 117389043397 (2 : ZMod 117389043397)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23, 1), (113, 2), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23, 1), (113, 2), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 117389043397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_113
      · exact prime_sixtySixBL_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117389043397) ^ 58694521698 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117389043397) ^ 39129681132 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117389043397) ^ 5103871452 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117389043397) ^ 1038841092 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 117389043397) ^ 31718196 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_121297980281 : Nat.Prime 121297980281 := by
  apply lucas_primality 121297980281 (3 : ZMod 121297980281)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (61, 1), (971, 1), (51197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (61, 1), (971, 1), (51197, 1)] : List FactorBlock).map factorBlockValue).prod) = 121297980281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_61
      · exact prime_sixtySixBL_971
      · exact prime_sixtySixBL_51197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 121297980281) ^ 60648990140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 121297980281) ^ 24259596056 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 121297980281) ^ 1988491480 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 121297980281) ^ 124920680 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 121297980281) ^ 2369240 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_134898715409 : Nat.Prime 134898715409 := by
  apply lucas_primality 134898715409 (3 : ZMod 134898715409)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (199, 1), (42367687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (199, 1), (42367687, 1)] : List FactorBlock).map factorBlockValue).prod) = 134898715409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_199
      · exact prime_sixtySixBL_42367687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 134898715409) ^ 67449357704 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 134898715409) ^ 677882992 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 134898715409) ^ 3184 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_150472629449 : Nat.Prime 150472629449 := by
  apply lucas_primality 150472629449 (3 : ZMod 150472629449)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (53, 1), (20875781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (53, 1), (20875781, 1)] : List FactorBlock).map factorBlockValue).prod) = 150472629449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_20875781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150472629449) ^ 75236314724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150472629449) ^ 8851331144 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150472629449) ^ 2839106216 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150472629449) ^ 7208 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_154573928539 : Nat.Prime 154573928539 := by
  apply lucas_primality 154573928539 (2 : ZMod 154573928539)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (16033, 1), (39191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (16033, 1), (39191, 1)] : List FactorBlock).map factorBlockValue).prod) = 154573928539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_16033
      · exact prime_sixtySixBL_39191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154573928539) ^ 77286964269 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 154573928539) ^ 51524642846 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 154573928539) ^ 3770095818 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 154573928539) ^ 9640986 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 154573928539) ^ 3944118 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_170762487769 : Nat.Prime 170762487769 := by
  apply lucas_primality 170762487769 (14 : ZMod 170762487769)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (790567073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (790567073, 1)] : List FactorBlock).map factorBlockValue).prod) = 170762487769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_790567073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 170762487769) ^ 85381243884 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 170762487769) ^ 56920829256 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (14 : ZMod 170762487769) ^ 216 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_178952422711 : Nat.Prime 178952422711 := by
  apply lucas_primality 178952422711 (3 : ZMod 178952422711)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6091, 1), (979327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6091, 1), (979327, 1)] : List FactorBlock).map factorBlockValue).prod) = 178952422711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_6091
      · exact prime_sixtySixBL_979327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 178952422711) ^ 89476211355 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 178952422711) ^ 59650807570 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 178952422711) ^ 35790484542 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 178952422711) ^ 29379810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 178952422711) ^ 182730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_179484641051 : Nat.Prime 179484641051 := by
  apply lucas_primality 179484641051 (2 : ZMod 179484641051)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (13, 1), (47, 1), (534101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (13, 1), (47, 1), (534101, 1)] : List FactorBlock).map factorBlockValue).prod) = 179484641051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_534101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 179484641051) ^ 89742320525 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 179484641051) ^ 35896928210 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 179484641051) ^ 16316785550 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 179484641051) ^ 13806510850 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 179484641051) ^ 3818822150 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 179484641051) ^ 336050 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_242777071657 : Nat.Prime 242777071657 := by
  apply lucas_primality 242777071657 (11 : ZMod 242777071657)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (109, 1), (4419271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (109, 1), (4419271, 1)] : List FactorBlock).map factorBlockValue).prod) = 242777071657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_109
      · exact prime_sixtySixBL_4419271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 242777071657) ^ 121388535828 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 242777071657) ^ 80925690552 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 242777071657) ^ 34682438808 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 242777071657) ^ 2227312584 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 242777071657) ^ 54936 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_246080846639 : Nat.Prime 246080846639 := by
  apply lucas_primality 246080846639 (11 : ZMod 246080846639)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (11185493029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (11185493029, 1)] : List FactorBlock).map factorBlockValue).prod) = 246080846639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_11185493029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 246080846639) ^ 123040423319 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 246080846639) ^ 22370986058 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 246080846639) ^ 22 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_265542719461 : Nat.Prime 265542719461 := by
  apply lucas_primality 265542719461 (10 : ZMod 265542719461)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (131, 1), (33784061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (131, 1), (33784061, 1)] : List FactorBlock).map factorBlockValue).prod) = 265542719461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_131
      · exact prime_sixtySixBL_33784061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 265542719461) ^ 132771359730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 265542719461) ^ 88514239820 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 265542719461) ^ 53108543892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 265542719461) ^ 2027043660 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 265542719461) ^ 7860 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_441608322359 : Nat.Prime 441608322359 := by
  apply lucas_primality 441608322359 (7 : ZMod 441608322359)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (237168809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (237168809, 1)] : List FactorBlock).map factorBlockValue).prod) = 441608322359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_237168809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 441608322359) ^ 220804161179 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 441608322359) ^ 63086903194 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 441608322359) ^ 23242543282 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 441608322359) ^ 1862 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_522074441353 : Nat.Prime 522074441353 := by
  apply lucas_primality 522074441353 (5 : ZMod 522074441353)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (1279594219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (1279594219, 1)] : List FactorBlock).map factorBlockValue).prod) = 522074441353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_1279594219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 522074441353) ^ 261037220676 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 522074441353) ^ 174024813784 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 522074441353) ^ 30710261256 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 522074441353) ^ 408 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_686112379003 : Nat.Prime 686112379003 := by
  apply lucas_primality 686112379003 (3 : ZMod 686112379003)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (2242197317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (2242197317, 1)] : List FactorBlock).map factorBlockValue).prod) = 686112379003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_2242197317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 686112379003) ^ 343056189501 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 686112379003) ^ 228704126334 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 686112379003) ^ 40359551706 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 686112379003) ^ 306 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_853935122021 : Nat.Prime 853935122021 := by
  apply lucas_primality 853935122021 (2 : ZMod 853935122021)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (401, 1), (106475701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (401, 1), (106475701, 1)] : List FactorBlock).map factorBlockValue).prod) = 853935122021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_401
      · exact prime_sixtySixBL_106475701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 853935122021) ^ 426967561010 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 853935122021) ^ 170787024404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 853935122021) ^ 2129514020 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 853935122021) ^ 8020 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_986412200737 : Nat.Prime 986412200737 := by
  apply lucas_primality 986412200737 (5 : ZMod 986412200737)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (88169, 1), (116539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (88169, 1), (116539, 1)] : List FactorBlock).map factorBlockValue).prod) = 986412200737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_88169
      · exact prime_sixtySixBL_116539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 986412200737) ^ 493206100368 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 986412200737) ^ 328804066912 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 986412200737) ^ 11187744 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 986412200737) ^ 8464224 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1330845102157 : Nat.Prime 1330845102157 := by
  apply lucas_primality 1330845102157 (5 : ZMod 1330845102157)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (110903758513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (110903758513, 1)] : List FactorBlock).map factorBlockValue).prod) = 1330845102157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_110903758513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1330845102157) ^ 665422551078 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1330845102157) ^ 443615034052 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1330845102157) ^ 12 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1880226347353 : Nat.Prime 1880226347353 := by
  apply lucas_primality 1880226347353 (5 : ZMod 1880226347353)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (29, 1), (117455419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (29, 1), (117455419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880226347353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_117455419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1880226347353) ^ 940113173676 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1880226347353) ^ 626742115784 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1880226347353) ^ 81748971624 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1880226347353) ^ 64835391288 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1880226347353) ^ 16008 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2413685013079 : Nat.Prime 2413685013079 := by
  apply lucas_primality 2413685013079 (3 : ZMod 2413685013079)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (306577, 1), (1312169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (306577, 1), (1312169, 1)] : List FactorBlock).map factorBlockValue).prod) = 2413685013079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_306577
      · exact prime_sixtySixBL_1312169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2413685013079) ^ 1206842506539 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2413685013079) ^ 804561671026 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2413685013079) ^ 7873014 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2413685013079) ^ 1839462 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2538442389317 : Nat.Prime 2538442389317 := by
  apply lucas_primality 2538442389317 (2 : ZMod 2538442389317)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (37330035137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (37330035137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2538442389317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_37330035137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2538442389317) ^ 1269221194658 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2538442389317) ^ 149320140548 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2538442389317) ^ 68 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2996621269553 : Nat.Prime 2996621269553 := by
  apply lucas_primality 2996621269553 (3 : ZMod 2996621269553)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (1818338149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (1818338149, 1)] : List FactorBlock).map factorBlockValue).prod) = 2996621269553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_103
      · exact prime_sixtySixBL_1818338149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2996621269553) ^ 1498310634776 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2996621269553) ^ 29093410384 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2996621269553) ^ 1648 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3440440878331 : Nat.Prime 3440440878331 := by
  apply lucas_primality 3440440878331 (3 : ZMod 3440440878331)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (72689, 1), (1577699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (72689, 1), (1577699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3440440878331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_72689
      · exact prime_sixtySixBL_1577699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3440440878331) ^ 1720220439165 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440440878331) ^ 1146813626110 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440440878331) ^ 688088175666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440440878331) ^ 47330970 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440440878331) ^ 2180670 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3489464323591 : Nat.Prime 3489464323591 := by
  apply lucas_primality 3489464323591 (6 : ZMod 3489464323591)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (89, 1), (10982483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (89, 1), (10982483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3489464323591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_89
      · exact prime_sixtySixBL_10982483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3489464323591) ^ 1744732161795 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 1163154774530 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 697892864718 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 498494903370 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 205262607270 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 39207464310 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3489464323591) ^ 317730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4435136295857 : Nat.Prime 4435136295857 := by
  apply lucas_primality 4435136295857 (3 : ZMod 4435136295857)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (39599431213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (39599431213, 1)] : List FactorBlock).map factorBlockValue).prod) = 4435136295857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_39599431213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4435136295857) ^ 2217568147928 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4435136295857) ^ 633590899408 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4435136295857) ^ 112 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5906080480031 : Nat.Prime 5906080480031 := by
  apply lucas_primality 5906080480031 (7 : ZMod 5906080480031)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (191, 1), (3092188733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (191, 1), (3092188733, 1)] : List FactorBlock).map factorBlockValue).prod) = 5906080480031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_191
      · exact prime_sixtySixBL_3092188733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5906080480031) ^ 2953040240015 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5906080480031) ^ 1181216096006 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5906080480031) ^ 30921887330 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5906080480031) ^ 1910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_6831480976169 : Nat.Prime 6831480976169 := by
  apply lucas_primality 6831480976169 (3 : ZMod 6831480976169)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (853935122021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (853935122021, 1)] : List FactorBlock).map factorBlockValue).prod) = 6831480976169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_853935122021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6831480976169) ^ 3415740488084 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6831480976169) ^ 8 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7698263877137 : Nat.Prime 7698263877137 := by
  apply lucas_primality 7698263877137 (3 : ZMod 7698263877137)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (421, 1), (811, 1), (28759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (421, 1), (811, 1), (28759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7698263877137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_421
      · exact prime_sixtySixBL_811
      · exact prime_sixtySixBL_28759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7698263877137) ^ 3849131938568 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7698263877137) ^ 1099751982448 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7698263877137) ^ 18285662416 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7698263877137) ^ 9492310576 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7698263877137) ^ 267681904 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7985070612943 : Nat.Prime 7985070612943 := by
  apply lucas_primality 7985070612943 (3 : ZMod 7985070612943)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1330845102157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1330845102157, 1)] : List FactorBlock).map factorBlockValue).prod) = 7985070612943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1330845102157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7985070612943) ^ 3992535306471 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7985070612943) ^ 2661690204314 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 7985070612943) ^ 6 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_9654740052317 : Nat.Prime 9654740052317 := by
  apply lucas_primality 9654740052317 (2 : ZMod 9654740052317)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2413685013079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2413685013079, 1)] : List FactorBlock).map factorBlockValue).prod) = 9654740052317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_2413685013079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9654740052317) ^ 4827370026158 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9654740052317) ^ 4 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_11701565716387 : Nat.Prime 11701565716387 := by
  apply lucas_primality 11701565716387 (3 : ZMod 11701565716387)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (15619, 1), (1372139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (15619, 1), (1372139, 1)] : List FactorBlock).map factorBlockValue).prod) = 11701565716387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_15619
      · exact prime_sixtySixBL_1372139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11701565716387) ^ 5850782858193 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11701565716387) ^ 3900521905462 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11701565716387) ^ 1671652245198 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11701565716387) ^ 900120439722 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11701565716387) ^ 749187894 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11701565716387) ^ 8527974 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_12411564223717 : Nat.Prime 12411564223717 := by
  apply lucas_primality 12411564223717 (6 : ZMod 12411564223717)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (100363, 1), (490741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (100363, 1), (490741, 1)] : List FactorBlock).map factorBlockValue).prod) = 12411564223717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_100363
      · exact prime_sixtySixBL_490741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12411564223717) ^ 6205782111858 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12411564223717) ^ 4137188074572 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12411564223717) ^ 1773080603388 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12411564223717) ^ 123666732 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12411564223717) ^ 25291476 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_19963969625581 : Nat.Prime 19963969625581 := by
  apply lucas_primality 19963969625581 (2 : ZMod 19963969625581)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (86183, 1), (124541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (86183, 1), (124541, 1)] : List FactorBlock).map factorBlockValue).prod) = 19963969625581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_86183
      · exact prime_sixtySixBL_124541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19963969625581) ^ 9981984812790 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19963969625581) ^ 6654656541860 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19963969625581) ^ 3992793925116 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19963969625581) ^ 643999020180 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19963969625581) ^ 231646260 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19963969625581) ^ 160300380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_20168508413087 : Nat.Prime 20168508413087 := by
  apply lucas_primality 20168508413087 (5 : ZMod 20168508413087)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (48250020127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (48250020127, 1)] : List FactorBlock).map factorBlockValue).prod) = 20168508413087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_48250020127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20168508413087) ^ 10084254206543 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20168508413087) ^ 1833500764826 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20168508413087) ^ 1061500442794 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 20168508413087) ^ 418 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_24180615848149 : Nat.Prime 24180615848149 := by
  apply lucas_primality 24180615848149 (2 : ZMod 24180615848149)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (197, 1), (587, 1), (17425361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (197, 1), (587, 1), (17425361, 1)] : List FactorBlock).map factorBlockValue).prod) = 24180615848149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_197
      · exact prime_sixtySixBL_587
      · exact prime_sixtySixBL_17425361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24180615848149) ^ 12090307924074 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24180615848149) ^ 8060205282716 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24180615848149) ^ 122744242884 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24180615848149) ^ 41193553404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24180615848149) ^ 1387668 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_28845034284839 : Nat.Prime 28845034284839 := by
  apply lucas_primality 28845034284839 (11 : ZMod 28845034284839)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (14741, 1), (51494461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (14741, 1), (51494461, 1)] : List FactorBlock).map factorBlockValue).prod) = 28845034284839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_14741
      · exact prime_sixtySixBL_51494461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 28845034284839) ^ 14422517142419 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28845034284839) ^ 1518159699202 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28845034284839) ^ 1956789518 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28845034284839) ^ 560158 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_34476401734039 : Nat.Prime 34476401734039 := by
  apply lucas_primality 34476401734039 (6 : ZMod 34476401734039)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (10242543593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (10242543593, 1)] : List FactorBlock).map factorBlockValue).prod) = 34476401734039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_10242543593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 34476401734039) ^ 17238200867019 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34476401734039) ^ 11492133911346 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34476401734039) ^ 3134218339458 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34476401734039) ^ 2028023631414 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34476401734039) ^ 3366 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_62810357824639 : Nat.Prime 62810357824639 := by
  apply lucas_primality 62810357824639 (6 : ZMod 62810357824639)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3489464323591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3489464323591, 1)] : List FactorBlock).map factorBlockValue).prod) = 62810357824639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_3489464323591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 62810357824639) ^ 31405178912319 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 62810357824639) ^ 20936785941546 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 62810357824639) ^ 18 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_69016938052583 : Nat.Prime 69016938052583 := by
  apply lucas_primality 69016938052583 (5 : ZMod 69016938052583)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (41, 1), (3593, 1), (62351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (41, 1), (3593, 1), (62351, 1)] : List FactorBlock).map factorBlockValue).prod) = 69016938052583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_3593
      · exact prime_sixtySixBL_62351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 69016938052583) ^ 34508469026291 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 69016938052583) ^ 5308995234814 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 69016938052583) ^ 4059819885446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 69016938052583) ^ 1683339952502 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 69016938052583) ^ 19208721974 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 69016938052583) ^ 1106909882 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_72071283395281 : Nat.Prime 72071283395281 := by
  apply lucas_primality 72071283395281 (43 : ZMod 72071283395281)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (53, 1), (435844723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (53, 1), (435844723, 1)] : List FactorBlock).map factorBlockValue).prod) = 72071283395281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_53
      · exact prime_sixtySixBL_435844723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 72071283395281) ^ 36035641697640 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (43 : ZMod 72071283395281) ^ 24023761131760 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (43 : ZMod 72071283395281) ^ 14414256679056 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (43 : ZMod 72071283395281) ^ 5543944876560 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (43 : ZMod 72071283395281) ^ 1359835535760 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (43 : ZMod 72071283395281) ^ 165360 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_96511901173973 : Nat.Prime 96511901173973 := by
  apply lucas_primality 96511901173973 (2 : ZMod 96511901173973)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (20549, 1), (3824651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (20549, 1), (3824651, 1)] : List FactorBlock).map factorBlockValue).prod) = 96511901173973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_307
      · exact prime_sixtySixBL_20549
      · exact prime_sixtySixBL_3824651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96511901173973) ^ 48255950586986 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96511901173973) ^ 314371013596 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96511901173973) ^ 4696671428 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 96511901173973) ^ 25234172 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_121419680053663 : Nat.Prime 121419680053663 := by
  apply lucas_primality 121419680053663 (5 : ZMod 121419680053663)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (89273, 1), (75560783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (89273, 1), (75560783, 1)] : List FactorBlock).map factorBlockValue).prod) = 121419680053663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_89273
      · exact prime_sixtySixBL_75560783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 121419680053663) ^ 60709840026831 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 121419680053663) ^ 40473226684554 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 121419680053663) ^ 1360094094 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 121419680053663) ^ 1606914 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_131978142858311 : Nat.Prime 131978142858311 := by
  apply lucas_primality 131978142858311 (7 : ZMod 131978142858311)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (29, 1), (47, 1), (1383273691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (29, 1), (47, 1), (1383273691, 1)] : List FactorBlock).map factorBlockValue).prod) = 131978142858311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_1383273691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 131978142858311) ^ 65989071429155 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 131978142858311) ^ 26395628571662 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 131978142858311) ^ 18854020408330 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 131978142858311) ^ 4550970443390 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 131978142858311) ^ 2808045592730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 131978142858311) ^ 95410 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_223885590465631 : Nat.Prime 223885590465631 := by
  apply lucas_primality 223885590465631 (6 : ZMod 223885590465631)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (258809, 1), (1517651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (258809, 1), (1517651, 1)] : List FactorBlock).map factorBlockValue).prod) = 223885590465631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_258809
      · exact prime_sixtySixBL_1517651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 223885590465631) ^ 111942795232815 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 223885590465631) ^ 74628530155210 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 223885590465631) ^ 44777118093126 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 223885590465631) ^ 11783452129770 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 223885590465631) ^ 865061070 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 223885590465631) ^ 147521130 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_294907066955863 : Nat.Prime 294907066955863 := by
  apply lucas_primality 294907066955863 (3 : ZMod 294907066955863)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1970183, 1), (24947519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1970183, 1), (24947519, 1)] : List FactorBlock).map factorBlockValue).prod) = 294907066955863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1970183
      · exact prime_sixtySixBL_24947519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 294907066955863) ^ 147453533477931 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294907066955863) ^ 98302355651954 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294907066955863) ^ 149685114 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294907066955863) ^ 11821098 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_295502109211271 : Nat.Prime 295502109211271 := by
  apply lucas_primality 295502109211271 (7 : ZMod 295502109211271)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (179, 1), (229, 1), (55453469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (179, 1), (229, 1), (55453469, 1)] : List FactorBlock).map factorBlockValue).prod) = 295502109211271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_179
      · exact prime_sixtySixBL_229
      · exact prime_sixtySixBL_55453469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 295502109211271) ^ 147751054605635 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 295502109211271) ^ 59100421842254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 295502109211271) ^ 22730931477790 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 295502109211271) ^ 1650849772130 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 295502109211271) ^ 1290402223630 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 295502109211271) ^ 5328830 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_300877112105173 : Nat.Prime 300877112105173 := by
  apply lucas_primality 300877112105173 (2 : ZMod 300877112105173)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (101, 1), (9194386753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (101, 1), (9194386753, 1)] : List FactorBlock).map factorBlockValue).prod) = 300877112105173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_101
      · exact prime_sixtySixBL_9194386753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 300877112105173) ^ 150438556052586 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 300877112105173) ^ 100292370701724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 300877112105173) ^ 2978981307972 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 300877112105173) ^ 32724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_307972522376143 : Nat.Prime 307972522376143 := by
  apply lucas_primality 307972522376143 (5 : ZMod 307972522376143)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97, 2), (419637121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97, 2), (419637121, 1)] : List FactorBlock).map factorBlockValue).prod) = 307972522376143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_419637121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 307972522376143) ^ 153986261188071 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 307972522376143) ^ 102657507458714 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 307972522376143) ^ 23690194028934 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 307972522376143) ^ 3174974457486 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 307972522376143) ^ 733902 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_421899663194543 : Nat.Prime 421899663194543 := by
  apply lucas_primality 421899663194543 (5 : ZMod 421899663194543)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 3), (61, 1), (67, 1), (326323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 3), (61, 1), (67, 1), (326323, 1)] : List FactorBlock).map factorBlockValue).prod) = 421899663194543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_61
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_326323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 421899663194543) ^ 210949831597271 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 421899663194543) ^ 32453820245734 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 421899663194543) ^ 18343463617154 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 421899663194543) ^ 6916387921222 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 421899663194543) ^ 6297009898426 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 421899663194543) ^ 1292889754 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_561240029423653 : Nat.Prime 561240029423653 := by
  apply lucas_primality 561240029423653 (2 : ZMod 561240029423653)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (71, 1), (28640540387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (71, 1), (28640540387, 1)] : List FactorBlock).map factorBlockValue).prod) = 561240029423653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_71
      · exact prime_sixtySixBL_28640540387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 561240029423653) ^ 280620014711826 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 561240029423653) ^ 187080009807884 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 561240029423653) ^ 24401740409724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 561240029423653) ^ 7904789146812 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 561240029423653) ^ 19596 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_808497329361791 : Nat.Prime 808497329361791 := by
  apply lucas_primality 808497329361791 (11 : ZMod 808497329361791)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (1880226347353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (1880226347353, 1)] : List FactorBlock).map factorBlockValue).prod) = 808497329361791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_43
      · exact prime_sixtySixBL_1880226347353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 808497329361791) ^ 404248664680895 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 808497329361791) ^ 161699465872358 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 808497329361791) ^ 18802263473530 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 808497329361791) ^ 430 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_843799326389087 : Nat.Prime 843799326389087 := by
  apply lucas_primality 843799326389087 (5 : ZMod 843799326389087)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (421899663194543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (421899663194543, 1)] : List FactorBlock).map factorBlockValue).prod) = 843799326389087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_421899663194543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 843799326389087) ^ 421899663194543 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 843799326389087) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1037571769098281 : Nat.Prime 1037571769098281 := by
  apply lucas_primality 1037571769098281 (3 : ZMod 1037571769098281)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (20347, 1), (98065087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (20347, 1), (98065087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037571769098281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_20347
      · exact prime_sixtySixBL_98065087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1037571769098281) ^ 518785884549140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037571769098281) ^ 207514353819656 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037571769098281) ^ 79813213007560 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037571769098281) ^ 50993845240 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037571769098281) ^ 10580440 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1220612616489451 : Nat.Prime 1220612616489451 := by
  apply lucas_primality 1220612616489451 (3 : ZMod 1220612616489451)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (5147, 1), (1581002029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (5147, 1), (1581002029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1220612616489451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_5147
      · exact prime_sixtySixBL_1581002029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1220612616489451) ^ 610306308244725 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1220612616489451) ^ 406870872163150 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1220612616489451) ^ 244122523297890 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1220612616489451) ^ 237150304350 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1220612616489451) ^ 772050 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1295730101419279 : Nat.Prime 1295730101419279 := by
  apply lucas_primality 1295730101419279 (3 : ZMod 1295730101419279)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2988373, 1), (10323583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2988373, 1), (10323583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295730101419279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_2988373
      · exact prime_sixtySixBL_10323583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1295730101419279) ^ 647865050709639 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295730101419279) ^ 431910033806426 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295730101419279) ^ 185104300202754 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295730101419279) ^ 433590486 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295730101419279) ^ 125511666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2767612989887621 : Nat.Prime 2767612989887621 := by
  apply lucas_primality 2767612989887621 (3 : ZMod 2767612989887621)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (29, 2), (8011, 1), (2934233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (29, 2), (8011, 1), (2934233, 1)] : List FactorBlock).map factorBlockValue).prod) = 2767612989887621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_8011
      · exact prime_sixtySixBL_2934233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2767612989887621) ^ 1383806494943810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767612989887621) ^ 553522597977524 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767612989887621) ^ 395373284269660 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767612989887621) ^ 95434930685780 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767612989887621) ^ 345476593420 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767612989887621) ^ 943215140 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3491511116663137 : Nat.Prime 3491511116663137 := by
  apply lucas_primality 3491511116663137 (10 : ZMod 3491511116663137)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (691, 1), (3229, 1), (2328617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (691, 1), (3229, 1), (2328617, 1)] : List FactorBlock).map factorBlockValue).prod) = 3491511116663137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_691
      · exact prime_sixtySixBL_3229
      · exact prime_sixtySixBL_2328617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3491511116663137) ^ 1745755558331568 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 3491511116663137) ^ 1163837038887712 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 3491511116663137) ^ 498787302380448 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 3491511116663137) ^ 5052838084896 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 3491511116663137) ^ 1081297961184 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 3491511116663137) ^ 1499392608 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4107754544107399 : Nat.Prime 4107754544107399 := by
  apply lucas_primality 4107754544107399 (3 : ZMod 4107754544107399)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2721013, 1), (251606941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2721013, 1), (251606941, 1)] : List FactorBlock).map factorBlockValue).prod) = 4107754544107399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_2721013
      · exact prime_sixtySixBL_251606941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4107754544107399) ^ 2053877272053699 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4107754544107399) ^ 1369251514702466 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4107754544107399) ^ 1509641646 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4107754544107399) ^ 16326078 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4214113817456531 : Nat.Prime 4214113817456531 := by
  apply lucas_primality 4214113817456531 (2 : ZMod 4214113817456531)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (293, 1), (21737, 1), (5089741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (293, 1), (21737, 1), (5089741, 1)] : List FactorBlock).map factorBlockValue).prod) = 4214113817456531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_293
      · exact prime_sixtySixBL_21737
      · exact prime_sixtySixBL_5089741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4214113817456531) ^ 2107056908728265 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214113817456531) ^ 842822763491306 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214113817456531) ^ 324162601342810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214113817456531) ^ 14382641015210 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214113817456531) ^ 193868234690 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214113817456531) ^ 827962330 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5665305037057417 : Nat.Prime 5665305037057417 := by
  apply lucas_primality 5665305037057417 (5 : ZMod 5665305037057417)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (137, 1), (190301, 1), (335341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (137, 1), (190301, 1), (335341, 1)] : List FactorBlock).map factorBlockValue).prod) = 5665305037057417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_137
      · exact prime_sixtySixBL_190301
      · exact prime_sixtySixBL_335341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5665305037057417) ^ 2832652518528708 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5665305037057417) ^ 1888435012352472 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5665305037057417) ^ 41352591511368 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5665305037057417) ^ 29770232616 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5665305037057417) ^ 16894161576 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7409267686959563 : Nat.Prime 7409267686959563 := by
  apply lucas_primality 7409267686959563 (2 : ZMod 7409267686959563)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (97, 1), (131, 1), (103483, 1), (148279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (97, 1), (131, 1), (103483, 1), (148279, 1)] : List FactorBlock).map factorBlockValue).prod) = 7409267686959563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_131
      · exact prime_sixtySixBL_103483
      · exact prime_sixtySixBL_148279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7409267686959563) ^ 3704633843479781 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409267686959563) ^ 389961457208398 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409267686959563) ^ 76384202958346 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409267686959563) ^ 56559295320302 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409267686959563) ^ 71598887614 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409267686959563) ^ 49968422278 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7424418159264619 : Nat.Prime 7424418159264619 := by
  apply lucas_primality 7424418159264619 (7 : ZMod 7424418159264619)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (4435136295857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (4435136295857, 1)] : List FactorBlock).map factorBlockValue).prod) = 7424418159264619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_4435136295857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7424418159264619) ^ 3712209079632309 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 7424418159264619) ^ 2474806053088206 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 7424418159264619) ^ 239497359976278 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 7424418159264619) ^ 1674 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_9149588079131063 : Nat.Prime 9149588079131063 := by
  apply lucas_primality 9149588079131063 (5 : ZMod 9149588079131063)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1151, 1), (409153, 1), (9714277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1151, 1), (409153, 1), (9714277, 1)] : List FactorBlock).map factorBlockValue).prod) = 9149588079131063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_1151
      · exact prime_sixtySixBL_409153
      · exact prime_sixtySixBL_9714277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9149588079131063) ^ 4574794039565531 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9149588079131063) ^ 7949251154762 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9149588079131063) ^ 22362265654 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 9149588079131063) ^ 941870206 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_14911187437295729 : Nat.Prime 14911187437295729 := by
  apply lucas_primality 14911187437295729 (3 : ZMod 14911187437295729)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (311, 1), (2996621269553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (311, 1), (2996621269553, 1)] : List FactorBlock).map factorBlockValue).prod) = 14911187437295729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_311
      · exact prime_sixtySixBL_2996621269553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14911187437295729) ^ 7455593718647864 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14911187437295729) ^ 47945940312848 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14911187437295729) ^ 4976 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_17165315239064359 : Nat.Prime 17165315239064359 := by
  apply lucas_primality 17165315239064359 (6 : ZMod 17165315239064359)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (986191, 1), (5264873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (986191, 1), (5264873, 1)] : List FactorBlock).map factorBlockValue).prod) = 17165315239064359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_986191
      · exact prime_sixtySixBL_5264873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17165315239064359) ^ 8582657619532179 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17165315239064359) ^ 5721771746354786 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17165315239064359) ^ 903437644161282 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17165315239064359) ^ 591907422036702 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17165315239064359) ^ 17405670138 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17165315239064359) ^ 3260347446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_23779087021325707 : Nat.Prime 23779087021325707 := by
  apply lucas_primality 23779087021325707 (3 : ZMod 23779087021325707)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11701, 1), (48386354893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11701, 1), (48386354893, 1)] : List FactorBlock).map factorBlockValue).prod) = 23779087021325707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_11701
      · exact prime_sixtySixBL_48386354893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23779087021325707) ^ 11889543510662853 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23779087021325707) ^ 7926362340441902 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23779087021325707) ^ 3397012431617958 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23779087021325707) ^ 2032226905506 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23779087021325707) ^ 491442 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_29509572901090493 : Nat.Prime 29509572901090493 := by
  apply lucas_primality 29509572901090493 (2 : ZMod 29509572901090493)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (19, 1), (29, 1), (5867, 1), (46573531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (19, 1), (29, 1), (5867, 1), (46573531, 1)] : List FactorBlock).map factorBlockValue).prod) = 29509572901090493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_5867
      · exact prime_sixtySixBL_46573531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29509572901090493) ^ 14754786450545246 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 29509572901090493) ^ 4215653271584356 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 29509572901090493) ^ 1553135415846868 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 29509572901090493) ^ 1017571479347948 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 29509572901090493) ^ 5029755053876 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 29509572901090493) ^ 633612532 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_31195668726579163 : Nat.Prime 31195668726579163 := by
  apply lucas_primality 31195668726579163 (3 : ZMod 31195668726579163)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3407, 1), (117389043397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3407, 1), (117389043397, 1)] : List FactorBlock).map factorBlockValue).prod) = 31195668726579163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_3407
      · exact prime_sixtySixBL_117389043397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31195668726579163) ^ 15597834363289581 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31195668726579163) ^ 10398556242193054 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31195668726579163) ^ 2399666825121474 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31195668726579163) ^ 9156345384966 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31195668726579163) ^ 265746 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_32276058385712833 : Nat.Prime 32276058385712833 := by
  apply lucas_primality 32276058385712833 (5 : ZMod 32276058385712833)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (31, 1), (239, 1), (5569, 1), (452689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (31, 1), (239, 1), (5569, 1), (452689, 1)] : List FactorBlock).map factorBlockValue).prod) = 32276058385712833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_239
      · exact prime_sixtySixBL_5569
      · exact prime_sixtySixBL_452689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32276058385712833) ^ 16138029192856416 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 32276058385712833) ^ 10758686128570944 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 32276058385712833) ^ 1041163173732672 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 32276058385712833) ^ 135046269396288 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 32276058385712833) ^ 5795665000128 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 32276058385712833) ^ 71298525888 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_35535231074319569 : Nat.Prime 35535231074319569 := by
  apply lucas_primality 35535231074319569 (3 : ZMod 35535231074319569)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (181, 1), (30637, 1), (13810721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (181, 1), (30637, 1), (13810721, 1)] : List FactorBlock).map factorBlockValue).prod) = 35535231074319569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_181
      · exact prime_sixtySixBL_30637
      · exact prime_sixtySixBL_13810721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35535231074319569) ^ 17767615537159784 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35535231074319569) ^ 1225352795666192 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35535231074319569) ^ 196327243504528 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35535231074319569) ^ 1159879592464 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 35535231074319569) ^ 2573017808 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_43747513430671837 : Nat.Prime 43747513430671837 := by
  apply lucas_primality 43747513430671837 (2 : ZMod 43747513430671837)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (1409, 1), (3049, 1), (31429679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (1409, 1), (3049, 1), (31429679, 1)] : List FactorBlock).map factorBlockValue).prod) = 43747513430671837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1409
      · exact prime_sixtySixBL_3049
      · exact prime_sixtySixBL_31429679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43747513430671837) ^ 21873756715335918 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 43747513430671837) ^ 14582504476890612 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 43747513430671837) ^ 31048625571804 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 43747513430671837) ^ 14348151338364 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 43747513430671837) ^ 1391917284 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_54036386069033197 : Nat.Prime 54036386069033197 := by
  apply lucas_primality 54036386069033197 (2 : ZMod 54036386069033197)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (199, 1), (3547, 1), (2126520287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (199, 1), (3547, 1), (2126520287, 1)] : List FactorBlock).map factorBlockValue).prod) = 54036386069033197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_199
      · exact prime_sixtySixBL_3547
      · exact prime_sixtySixBL_2126520287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54036386069033197) ^ 27018193034516598 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54036386069033197) ^ 18012128689677732 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54036386069033197) ^ 271539628487604 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54036386069033197) ^ 15234391336068 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 54036386069033197) ^ 25410708 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_59019145802180987 : Nat.Prime 59019145802180987 := by
  apply lucas_primality 59019145802180987 (2 : ZMod 59019145802180987)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29509572901090493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29509572901090493, 1)] : List FactorBlock).map factorBlockValue).prod) = 59019145802180987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_29509572901090493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 59019145802180987) ^ 29509572901090493 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 59019145802180987) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_76605258199343899 : Nat.Prime 76605258199343899 := by
  apply lucas_primality 76605258199343899 (7 : ZMod 76605258199343899)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (342553, 1), (1202313881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (342553, 1), (1202313881, 1)] : List FactorBlock).map factorBlockValue).prod) = 76605258199343899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_31
      · exact prime_sixtySixBL_342553
      · exact prime_sixtySixBL_1202313881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76605258199343899) ^ 38302629099671949 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 76605258199343899) ^ 25535086066447966 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 76605258199343899) ^ 2471137361269158 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 76605258199343899) ^ 223630381866 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 76605258199343899) ^ 63714858 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_83224190319780091 : Nat.Prime 83224190319780091 := by
  apply lucas_primality 83224190319780091 (3 : ZMod 83224190319780091)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (1039, 1), (5372252141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (71, 1), (1039, 1), (5372252141, 1)] : List FactorBlock).map factorBlockValue).prod) = 83224190319780091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_71
      · exact prime_sixtySixBL_1039
      · exact prime_sixtySixBL_5372252141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83224190319780091) ^ 41612095159890045 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 27741396773260030 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 16644838063956018 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 11889170045682870 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 1172171694644790 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 80100279422310 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 83224190319780091) ^ 15491490 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_107678349777317591 : Nat.Prime 107678349777317591 := by
  apply lucas_primality 107678349777317591 (31 : ZMod 107678349777317591)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13013941, 1), (827407699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13013941, 1), (827407699, 1)] : List FactorBlock).map factorBlockValue).prod) = 107678349777317591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_13013941
      · exact prime_sixtySixBL_827407699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 107678349777317591) ^ 53839174888658795 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (31 : ZMod 107678349777317591) ^ 21535669955463518 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (31 : ZMod 107678349777317591) ^ 8274076990 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (31 : ZMod 107678349777317591) ^ 130139410 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_122748920177812853 : Nat.Prime 122748920177812853 := by
  apply lucas_primality 122748920177812853 (3 : ZMod 122748920177812853)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (157, 1), (2538442389317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (157, 1), (2538442389317, 1)] : List FactorBlock).map factorBlockValue).prod) = 122748920177812853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_157
      · exact prime_sixtySixBL_2538442389317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 122748920177812853) ^ 61374460088906426 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 122748920177812853) ^ 17535560025401836 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 122748920177812853) ^ 11158992743437532 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 122748920177812853) ^ 781840255909636 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 122748920177812853) ^ 48356 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_146924785791851479 : Nat.Prime 146924785791851479 := by
  apply lucas_primality 146924785791851479 (3 : ZMod 146924785791851479)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (1493, 1), (150472629449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (1493, 1), (150472629449, 1)] : List FactorBlock).map factorBlockValue).prod) = 146924785791851479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_109
      · exact prime_sixtySixBL_1493
      · exact prime_sixtySixBL_150472629449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 146924785791851479) ^ 73462392895925739 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146924785791851479) ^ 48974928597283826 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146924785791851479) ^ 1347933814604142 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146924785791851479) ^ 98409099659646 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146924785791851479) ^ 976422 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_148185353739191261 : Nat.Prime 148185353739191261 := by
  apply lucas_primality 148185353739191261 (3 : ZMod 148185353739191261)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7409267686959563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7409267686959563, 1)] : List FactorBlock).map factorBlockValue).prod) = 148185353739191261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_7409267686959563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 148185353739191261) ^ 74092676869595630 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 148185353739191261) ^ 29637070747838252 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 148185353739191261) ^ 20 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_150419225799379177 : Nat.Prime 150419225799379177 := by
  apply lucas_primality 150419225799379177 (5 : ZMod 150419225799379177)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (52147201, 1), (120187999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (52147201, 1), (120187999, 1)] : List FactorBlock).map factorBlockValue).prod) = 150419225799379177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_52147201
      · exact prime_sixtySixBL_120187999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 150419225799379177) ^ 75209612899689588 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 150419225799379177) ^ 50139741933126392 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 150419225799379177) ^ 2884511976 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 150419225799379177) ^ 1251532824 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_167390389785835039 : Nat.Prime 167390389785835039 := by
  apply lucas_primality 167390389785835039 (3 : ZMod 167390389785835039)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (149, 1), (395543, 1), (4880087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (149, 1), (395543, 1), (4880087, 1)] : List FactorBlock).map factorBlockValue).prod) = 167390389785835039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_149
      · exact prime_sixtySixBL_395543
      · exact prime_sixtySixBL_4880087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 167390389785835039) ^ 83695194892917519 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 167390389785835039) ^ 55796796595278346 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 167390389785835039) ^ 1725674121503454 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 167390389785835039) ^ 1123425434804262 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 167390389785835039) ^ 423191384466 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 167390389785835039) ^ 34300697874 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_213019603954706603 : Nat.Prime 213019603954706603 := by
  apply lucas_primality 213019603954706603 (2 : ZMod 213019603954706603)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (10279939, 1), (69536491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (10279939, 1), (69536491, 1)] : List FactorBlock).map factorBlockValue).prod) = 213019603954706603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_149
      · exact prime_sixtySixBL_10279939
      · exact prime_sixtySixBL_69536491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 213019603954706603) ^ 106509801977353301 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 213019603954706603) ^ 1429661771508098 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 213019603954706603) ^ 20721874318 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 213019603954706603) ^ 3063421822 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_247104427507920557 : Nat.Prime 247104427507920557 := by
  apply lucas_primality 247104427507920557 (2 : ZMod 247104427507920557)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (433, 1), (1949, 1), (1493910983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (433, 1), (1949, 1), (1493910983, 1)] : List FactorBlock).map factorBlockValue).prod) = 247104427507920557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_433
      · exact prime_sixtySixBL_1949
      · exact prime_sixtySixBL_1493910983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 247104427507920557) ^ 123552213753960278 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 247104427507920557) ^ 35300632501131508 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 247104427507920557) ^ 570679971149932 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 247104427507920557) ^ 126785237305244 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 247104427507920557) ^ 165407732 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_283994734870024517 : Nat.Prime 283994734870024517 := by
  apply lucas_primality 283994734870024517 (2 : ZMod 283994734870024517)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (131, 1), (653, 1), (63844349731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (131, 1), (653, 1), (63844349731, 1)] : List FactorBlock).map factorBlockValue).prod) = 283994734870024517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_131
      · exact prime_sixtySixBL_653
      · exact prime_sixtySixBL_63844349731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 283994734870024517) ^ 141997367435012258 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 283994734870024517) ^ 21845748836155732 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 283994734870024517) ^ 2167898739465836 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 283994734870024517) ^ 434907710367572 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 283994734870024517) ^ 4448236 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_748166810536952771 : Nat.Prime 748166810536952771 := by
  apply lucas_primality 748166810536952771 (2 : ZMod 748166810536952771)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (438133, 1), (170762487769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (438133, 1), (170762487769, 1)] : List FactorBlock).map factorBlockValue).prod) = 748166810536952771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_438133
      · exact prime_sixtySixBL_170762487769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 748166810536952771) ^ 374083405268476385 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 748166810536952771) ^ 149633362107390554 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 748166810536952771) ^ 1707624877690 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 748166810536952771) ^ 4381330 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_766052581993438991 : Nat.Prime 766052581993438991 := by
  apply lucas_primality 766052581993438991 (17 : ZMod 766052581993438991)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (76605258199343899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (76605258199343899, 1)] : List FactorBlock).map factorBlockValue).prod) = 766052581993438991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_76605258199343899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 766052581993438991) ^ 383026290996719495 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 766052581993438991) ^ 153210516398687798 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (17 : ZMod 766052581993438991) ^ 10 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1067909692544708561 : Nat.Prime 1067909692544708561 := by
  apply lucas_primality 1067909692544708561 (3 : ZMod 1067909692544708561)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (73, 1), (2843, 1), (16069, 1), (4002727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (73, 1), (2843, 1), (16069, 1), (4002727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067909692544708561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_2843
      · exact prime_sixtySixBL_16069
      · exact prime_sixtySixBL_4002727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1067909692544708561) ^ 533954846272354280 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067909692544708561) ^ 213581938508941712 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067909692544708561) ^ 14628899897872720 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067909692544708561) ^ 375627749751920 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067909692544708561) ^ 66457756708240 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067909692544708561) ^ 266795535280 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1348905868895236271 : Nat.Prime 1348905868895236271 := by
  apply lucas_primality 1348905868895236271 (7 : ZMod 1348905868895236271)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (67, 1), (97, 1), (441608322359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (67, 1), (97, 1), (441608322359, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348905868895236271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_441608322359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1348905868895236271) ^ 674452934447618135 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1348905868895236271) ^ 269781173779047254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1348905868895236271) ^ 28700124870111410 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1348905868895236271) ^ 20132923416346810 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1348905868895236271) ^ 13906246071084910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1348905868895236271) ^ 3054530 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1394656047301929773 : Nat.Prime 1394656047301929773 := by
  apply lucas_primality 1394656047301929773 (2 : ZMod 1394656047301929773)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (613, 1), (8647, 1), (58153, 1), (1131121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (613, 1), (8647, 1), (58153, 1), (1131121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1394656047301929773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_613
      · exact prime_sixtySixBL_8647
      · exact prime_sixtySixBL_58153
      · exact prime_sixtySixBL_1131121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1394656047301929773) ^ 697328023650964886 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394656047301929773) ^ 2275132214195644 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394656047301929773) ^ 161287850965876 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394656047301929773) ^ 23982529659724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1394656047301929773) ^ 1232985725932 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1465304290093910137 : Nat.Prime 1465304290093910137 := by
  apply lucas_primality 1465304290093910137 (15 : ZMod 1465304290093910137)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (101, 1), (15173, 1), (3064646561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (101, 1), (15173, 1), (3064646561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1465304290093910137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_101
      · exact prime_sixtySixBL_15173
      · exact prime_sixtySixBL_3064646561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 1465304290093910137) ^ 732652145046955068 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (15 : ZMod 1465304290093910137) ^ 488434763364636712 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (15 : ZMod 1465304290093910137) ^ 112715714622608472 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (15 : ZMod 1465304290093910137) ^ 14507963268256536 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (15 : ZMod 1465304290093910137) ^ 96573142430232 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (15 : ZMod 1465304290093910137) ^ 478131576 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1490932596828650567 : Nat.Prime 1490932596828650567 := by
  apply lucas_primality 1490932596828650567 (5 : ZMod 1490932596828650567)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (757429, 1), (4083843047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (757429, 1), (4083843047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1490932596828650567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_241
      · exact prime_sixtySixBL_757429
      · exact prime_sixtySixBL_4083843047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1490932596828650567) ^ 745466298414325283 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1490932596828650567) ^ 6186442310492326 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1490932596828650567) ^ 1968412348654 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1490932596828650567) ^ 365080778 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1496333621073905543 : Nat.Prime 1496333621073905543 := by
  apply lucas_primality 1496333621073905543 (5 : ZMod 1496333621073905543)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (748166810536952771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (748166810536952771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1496333621073905543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_748166810536952771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1496333621073905543) ^ 748166810536952771 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1496333621073905543) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2260900092040934797 : Nat.Prime 2260900092040934797 := by
  apply lucas_primality 2260900092040934797 (2 : ZMod 2260900092040934797)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (73, 1), (449, 1), (1319, 1), (484220999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (73, 1), (449, 1), (1319, 1), (484220999, 1)] : List FactorBlock).map factorBlockValue).prod) = 2260900092040934797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_449
      · exact prime_sixtySixBL_1319
      · exact prime_sixtySixBL_484220999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2260900092040934797) ^ 1130450046020467398 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2260900092040934797) ^ 753633364013644932 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2260900092040934797) ^ 30971234137547052 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2260900092040934797) ^ 5035412231717004 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2260900092040934797) ^ 1714101661896084 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2260900092040934797) ^ 4669149204 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2964129041357617213 : Nat.Prime 2964129041357617213 := by
  apply lucas_primality 2964129041357617213 (6 : ZMod 2964129041357617213)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (808153, 1), (11320314871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (808153, 1), (11320314871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2964129041357617213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_808153
      · exact prime_sixtySixBL_11320314871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2964129041357617213) ^ 1482064520678808606 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2964129041357617213) ^ 988043013785872404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2964129041357617213) ^ 3667782018204 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2964129041357617213) ^ 261841572 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2996070851512083277 : Nat.Prime 2996070851512083277 := by
  apply lucas_primality 2996070851512083277 (5 : ZMod 2996070851512083277)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83224190319780091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83224190319780091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2996070851512083277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_83224190319780091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2996070851512083277) ^ 1498035425756041638 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2996070851512083277) ^ 998690283837361092 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2996070851512083277) ^ 36 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3150787103356440293 : Nat.Prime 3150787103356440293 := by
  apply lucas_primality 3150787103356440293 (2 : ZMod 3150787103356440293)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2671, 1), (294907066955863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2671, 1), (294907066955863, 1)] : List FactorBlock).map factorBlockValue).prod) = 3150787103356440293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_2671
      · exact prime_sixtySixBL_294907066955863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3150787103356440293) ^ 1575393551678220146 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3150787103356440293) ^ 1179628267823452 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3150787103356440293) ^ 10684 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4245422492783404811 : Nat.Prime 4245422492783404811 := by
  apply lucas_primality 4245422492783404811 (2 : ZMod 4245422492783404811)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (673, 1), (7985070612943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (673, 1), (7985070612943, 1)] : List FactorBlock).map factorBlockValue).prod) = 4245422492783404811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_79
      · exact prime_sixtySixBL_673
      · exact prime_sixtySixBL_7985070612943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4245422492783404811) ^ 2122711246391702405 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4245422492783404811) ^ 849084498556680962 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4245422492783404811) ^ 53739525225106390 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4245422492783404811) ^ 6308205784224970 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4245422492783404811) ^ 531670 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4991153988214019677 : Nat.Prime 4991153988214019677 := by
  apply lucas_primality 4991153988214019677 (2 : ZMod 4991153988214019677)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (557, 1), (7698263877137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (557, 1), (7698263877137, 1)] : List FactorBlock).map factorBlockValue).prod) = 4991153988214019677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_97
      · exact prime_sixtySixBL_557
      · exact prime_sixtySixBL_7698263877137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4991153988214019677) ^ 2495576994107009838 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4991153988214019677) ^ 1663717996071339892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4991153988214019677) ^ 51455195754783708 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4991153988214019677) ^ 8960779152987468 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4991153988214019677) ^ 648348 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5352897575291494619 : Nat.Prime 5352897575291494619 := by
  apply lucas_primality 5352897575291494619 (2 : ZMod 5352897575291494619)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (66678137, 1), (3087678889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (66678137, 1), (3087678889, 1)] : List FactorBlock).map factorBlockValue).prod) = 5352897575291494619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_66678137
      · exact prime_sixtySixBL_3087678889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5352897575291494619) ^ 2676448787645747309 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5352897575291494619) ^ 411761351945499586 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5352897575291494619) ^ 80279651114 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5352897575291494619) ^ 1733631562 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5913880251878086483 : Nat.Prime 5913880251878086483 := by
  apply lucas_primality 5913880251878086483 (3 : ZMod 5913880251878086483)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23366729, 1), (42181629643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23366729, 1), (42181629643, 1)] : List FactorBlock).map factorBlockValue).prod) = 5913880251878086483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23366729
      · exact prime_sixtySixBL_42181629643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5913880251878086483) ^ 2956940125939043241 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5913880251878086483) ^ 1971293417292695494 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5913880251878086483) ^ 253089777858 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5913880251878086483) ^ 140200374 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_9927668902759025683 : Nat.Prime 9927668902759025683 := by
  apply lucas_primality 9927668902759025683 (11 : ZMod 9927668902759025683)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (150419225799379177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (150419225799379177, 1)] : List FactorBlock).map factorBlockValue).prod) = 9927668902759025683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_150419225799379177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9927668902759025683) ^ 4963834451379512841 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9927668902759025683) ^ 3309222967586341894 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9927668902759025683) ^ 902515354796275062 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9927668902759025683) ^ 66 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_25262690446260503851 : Nat.Prime 25262690446260503851 := by
  apply lucas_primality 25262690446260503851 (2 : ZMod 25262690446260503851)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (41, 1), (4107754544107399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (41, 1), (4107754544107399, 1)] : List FactorBlock).map factorBlockValue).prod) = 25262690446260503851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_4107754544107399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25262690446260503851) ^ 12631345223130251925 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 25262690446260503851) ^ 8420896815420167950 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 25262690446260503851) ^ 5052538089252100770 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 25262690446260503851) ^ 616163181616109850 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 25262690446260503851) ^ 6150 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_31371302305376460727 : Nat.Prime 31371302305376460727 := by
  apply lucas_primality 31371302305376460727 (3 : ZMod 31371302305376460727)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (16633, 1), (24180615848149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (16633, 1), (24180615848149, 1)] : List FactorBlock).map factorBlockValue).prod) = 31371302305376460727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_16633
      · exact prime_sixtySixBL_24180615848149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31371302305376460727) ^ 15685651152688230363 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31371302305376460727) ^ 10457100768458820242 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31371302305376460727) ^ 2413177100413573902 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31371302305376460727) ^ 1886088036155622 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31371302305376460727) ^ 1297374 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_33265651169127716107 : Nat.Prime 33265651169127716107 := by
  apply lucas_primality 33265651169127716107 (3 : ZMod 33265651169127716107)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (2633, 1), (28845034284839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (2633, 1), (28845034284839, 1)] : List FactorBlock).map factorBlockValue).prod) = 33265651169127716107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_2633
      · exact prime_sixtySixBL_28845034284839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33265651169127716107) ^ 16632825584563858053 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33265651169127716107) ^ 11088550389709238702 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33265651169127716107) ^ 455693851631886522 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33265651169127716107) ^ 12634125016759482 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 33265651169127716107) ^ 1153254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_39288049153302341827 : Nat.Prime 39288049153302341827 := by
  apply lucas_primality 39288049153302341827 (3 : ZMod 39288049153302341827)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (19, 1), (37, 1), (4049, 1), (4057168579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (19, 1), (37, 1), (4049, 1), (4057168579, 1)] : List FactorBlock).map factorBlockValue).prod) = 39288049153302341827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_19
      · exact prime_sixtySixBL_37
      · exact prime_sixtySixBL_4049
      · exact prime_sixtySixBL_4057168579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39288049153302341827) ^ 19644024576651170913 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 13096016384434113942 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 5612578450471763118 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 2067792060700123254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 1061839166305468698 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 9703148716547874 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 39288049153302341827) ^ 9683612694 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_49140043632762007267 : Nat.Prime 49140043632762007267 := by
  apply lucas_primality 49140043632762007267 (2 : ZMod 49140043632762007267)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (17, 1), (73, 1), (181, 1), (34871, 1), (2880467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (17, 1), (73, 1), (181, 1), (34871, 1), (2880467, 1)] : List FactorBlock).map factorBlockValue).prod) = 49140043632762007267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_181
      · exact prime_sixtySixBL_34871
      · exact prime_sixtySixBL_2880467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49140043632762007267) ^ 24570021816381003633 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 16380014544254002422 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 4467276693887455206 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 2890590801927176898 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 673151282640575442 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 271491953772165786 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 1409195137299246 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 49140043632762007267) ^ 17059748864598 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_59566013416554154099 : Nat.Prime 59566013416554154099 := by
  apply lucas_primality 59566013416554154099 (7 : ZMod 59566013416554154099)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9927668902759025683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9927668902759025683, 1)] : List FactorBlock).map factorBlockValue).prod) = 59566013416554154099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_9927668902759025683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 59566013416554154099) ^ 29783006708277077049 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 59566013416554154099) ^ 19855337805518051366 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 59566013416554154099) ^ 6 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_72859122633341966249 : Nat.Prime 72859122633341966249 := by
  apply lucas_primality 72859122633341966249 (3 : ZMod 72859122633341966249)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (383, 1), (23779087021325707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (383, 1), (23779087021325707, 1)] : List FactorBlock).map factorBlockValue).prod) = 72859122633341966249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_383
      · exact prime_sixtySixBL_23779087021325707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72859122633341966249) ^ 36429561316670983124 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 72859122633341966249) ^ 190232696170605656 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 72859122633341966249) ^ 3064 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_96333188918580451823 : Nat.Prime 96333188918580451823 := by
  apply lucas_primality 96333188918580451823 (5 : ZMod 96333188918580451823)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39461, 1), (1220612616489451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39461, 1), (1220612616489451, 1)] : List FactorBlock).map factorBlockValue).prod) = 96333188918580451823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_39461
      · exact prime_sixtySixBL_1220612616489451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 96333188918580451823) ^ 48166594459290225911 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 96333188918580451823) ^ 2441225232978902 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 96333188918580451823) ^ 78922 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_119566083621150844973 : Nat.Prime 119566083621150844973 := by
  apply lucas_primality 119566083621150844973 (3 : ZMod 119566083621150844973)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (4999, 1), (11701565716387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (4999, 1), (11701565716387, 1)] : List FactorBlock).map factorBlockValue).prod) = 119566083621150844973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_73
      · exact prime_sixtySixBL_4999
      · exact prime_sixtySixBL_11701565716387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119566083621150844973) ^ 59783041810575422486 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 119566083621150844973) ^ 17080869088735834996 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 119566083621150844973) ^ 1637891556454121164 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 119566083621150844973) ^ 23918000324295028 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 119566083621150844973) ^ 10217956 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_137334537422354380777 : Nat.Prime 137334537422354380777 := by
  apply lucas_primality 137334537422354380777 (13 : ZMod 137334537422354380777)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1051, 1), (71909, 1), (75715110761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1051, 1), (71909, 1), (75715110761, 1)] : List FactorBlock).map factorBlockValue).prod) = 137334537422354380777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1051
      · exact prime_sixtySixBL_71909
      · exact prime_sixtySixBL_75715110761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 137334537422354380777) ^ 68667268711177190388 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 137334537422354380777) ^ 45778179140784793592 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 137334537422354380777) ^ 130670349593105976 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 137334537422354380777) ^ 1909837953835464 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 137334537422354380777) ^ 1813832616 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_377843488961294990149 : Nat.Prime 377843488961294990149 := by
  apply lucas_primality 377843488961294990149 (2 : ZMod 377843488961294990149)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4241, 1), (7424418159264619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4241, 1), (7424418159264619, 1)] : List FactorBlock).map factorBlockValue).prod) = 377843488961294990149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_4241
      · exact prime_sixtySixBL_7424418159264619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 377843488961294990149) ^ 188921744480647495074 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 377843488961294990149) ^ 125947829653764996716 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 377843488961294990149) ^ 89093017911175428 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 377843488961294990149) ^ 50892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_563824369515700812773 : Nat.Prime 563824369515700812773 := by
  apply lucas_primality 563824369515700812773 (2 : ZMod 563824369515700812773)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 1), (47, 1), (489109, 1), (13595769641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 1), (47, 1), (489109, 1), (13595769641, 1)] : List FactorBlock).map factorBlockValue).prod) = 563824369515700812773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_41
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_489109
      · exact prime_sixtySixBL_13595769641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 563824369515700812773) ^ 281912184757850406386 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 563824369515700812773) ^ 51256760865063710252 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 563824369515700812773) ^ 13751813890626849092 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 563824369515700812773) ^ 11996263181185123676 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 563824369515700812773) ^ 1152758116321108 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 563824369515700812773) ^ 41470573892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_674909095062884289397 : Nat.Prime 674909095062884289397 := by
  apply lucas_primality 674909095062884289397 (2 : ZMod 674909095062884289397)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (4357, 1), (561240029423653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (4357, 1), (561240029423653, 1)] : List FactorBlock).map factorBlockValue).prod) = 674909095062884289397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_4357
      · exact prime_sixtySixBL_561240029423653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 674909095062884289397) ^ 337454547531442144698 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 674909095062884289397) ^ 224969698354294763132 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 674909095062884289397) ^ 29343873698386273452 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 674909095062884289397) ^ 154902248120928228 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 674909095062884289397) ^ 1202532 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_830724448752158220709 : Nat.Prime 830724448752158220709 := by
  apply lucas_primality 830724448752158220709 (13 : ZMod 830724448752158220709)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (67, 1), (89, 1), (239, 1), (503, 1), (1970829121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (67, 1), (89, 1), (239, 1), (503, 1), (1970829121, 1)] : List FactorBlock).map factorBlockValue).prod) = 830724448752158220709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_67
      · exact prime_sixtySixBL_89
      · exact prime_sixtySixBL_239
      · exact prime_sixtySixBL_503
      · exact prime_sixtySixBL_1970829121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 830724448752158220709) ^ 415362224376079110354 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 276908149584052740236 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 118674921250308317244 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 12398872369435197324 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 9333982570248968772 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 3475834513607356572 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 1651539659547034236 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 830724448752158220709) ^ 421510134948 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_984891494799364406173 : Nat.Prime 984891494799364406173 := by
  apply lucas_primality 984891494799364406173 (2 : ZMod 984891494799364406173)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (121501, 1), (231131, 1), (2922598051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (121501, 1), (231131, 1), (2922598051, 1)] : List FactorBlock).map factorBlockValue).prod) = 984891494799364406173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_121501
      · exact prime_sixtySixBL_231131
      · exact prime_sixtySixBL_2922598051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 984891494799364406173) ^ 492445747399682203086 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 984891494799364406173) ^ 328297164933121468724 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 984891494799364406173) ^ 8106036121508172 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 984891494799364406173) ^ 4261183029534612 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 984891494799364406173) ^ 336991771572 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1127648739031401625547 : Nat.Prime 1127648739031401625547 := by
  apply lucas_primality 1127648739031401625547 (2 : ZMod 1127648739031401625547)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (563824369515700812773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (563824369515700812773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1127648739031401625547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_563824369515700812773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1127648739031401625547) ^ 563824369515700812773 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1127648739031401625547) ^ 2 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1178394376655308669583 : Nat.Prime 1178394376655308669583 := by
  apply lucas_primality 1178394376655308669583 (10 : ZMod 1178394376655308669583)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (3150787103356440293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (3150787103356440293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1178394376655308669583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_3150787103356440293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1178394376655308669583) ^ 589197188327654334791 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1178394376655308669583) ^ 107126761514118969962 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1178394376655308669583) ^ 69317316273841686446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1178394376655308669583) ^ 374 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1588873569220959446459 : Nat.Prime 1588873569220959446459 := by
  apply lucas_primality 1588873569220959446459 (2 : ZMod 1588873569220959446459)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (569, 1), (26080619, 1), (103547267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (569, 1), (26080619, 1), (103547267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588873569220959446459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_11
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_569
      · exact prime_sixtySixBL_26080619
      · exact prime_sixtySixBL_103547267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1588873569220959446459) ^ 794436784610479723229 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588873569220959446459) ^ 144443051747359949678 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588873569220959446459) ^ 33805820621722541414 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588873569220959446459) ^ 2792396430968294282 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588873569220959446459) ^ 60921620350382 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588873569220959446459) ^ 15344427866174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1696743019047328819153 : Nat.Prime 1696743019047328819153 := by
  apply lucas_primality 1696743019047328819153 (5 : ZMod 1696743019047328819153)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (27281, 1), (1295730101419279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (27281, 1), (1295730101419279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1696743019047328819153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_27281
      · exact prime_sixtySixBL_1295730101419279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1696743019047328819153) ^ 848371509523664409576 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1696743019047328819153) ^ 565581006349109606384 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1696743019047328819153) ^ 62195044868125392 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1696743019047328819153) ^ 1309488 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2340065897360665887613 : Nat.Prime 2340065897360665887613 := by
  apply lucas_primality 2340065897360665887613 (2 : ZMod 2340065897360665887613)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1811, 1), (107678349777317591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1811, 1), (107678349777317591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2340065897360665887613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_1811
      · exact prime_sixtySixBL_107678349777317591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2340065897360665887613) ^ 1170032948680332943806 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340065897360665887613) ^ 780021965786888629204 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340065897360665887613) ^ 1292140197327811092 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340065897360665887613) ^ 21732 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3188407946893204193623 : Nat.Prime 3188407946893204193623 := by
  apply lucas_primality 3188407946893204193623 (6 : ZMod 3188407946893204193623)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (16747, 1), (5517013, 1), (639056263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (16747, 1), (5517013, 1), (639056263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3188407946893204193623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_16747
      · exact prime_sixtySixBL_5517013
      · exact prime_sixtySixBL_639056263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3188407946893204193623) ^ 1594203973446602096811 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3188407946893204193623) ^ 1062802648964401397874 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3188407946893204193623) ^ 190386812377930626 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3188407946893204193623) ^ 577922862768894 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3188407946893204193623) ^ 4989244502394 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3650125416121793075821 : Nat.Prime 3650125416121793075821 := by
  apply lucas_primality 3650125416121793075821 (6 : ZMod 3650125416121793075821)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (250581421, 1), (242777071657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (250581421, 1), (242777071657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3650125416121793075821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_250581421
      · exact prime_sixtySixBL_242777071657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3650125416121793075821) ^ 1825062708060896537910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3650125416121793075821) ^ 1216708472040597691940 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3650125416121793075821) ^ 730025083224358615164 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3650125416121793075821) ^ 14566624299420 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 3650125416121793075821) ^ 15034885260 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4058056780352431832617 : Nat.Prime 4058056780352431832617 := by
  apply lucas_primality 4058056780352431832617 (5 : ZMod 4058056780352431832617)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (113, 1), (1496333621073905543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (113, 1), (1496333621073905543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4058056780352431832617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_113
      · exact prime_sixtySixBL_1496333621073905543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4058056780352431832617) ^ 2029028390176215916308 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4058056780352431832617) ^ 1352685593450810610872 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4058056780352431832617) ^ 35912006905773733032 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4058056780352431832617) ^ 2712 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_6584083614375689183119 : Nat.Prime 6584083614375689183119 := by
  apply lucas_primality 6584083614375689183119 (6 : ZMod 6584083614375689183119)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (521023, 1), (300877112105173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (521023, 1), (300877112105173, 1)] : List FactorBlock).map factorBlockValue).prod) = 6584083614375689183119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_521023
      · exact prime_sixtySixBL_300877112105173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6584083614375689183119) ^ 3292041807187844591559 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 6584083614375689183119) ^ 2194694538125229727706 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 6584083614375689183119) ^ 940583373482241311874 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 6584083614375689183119) ^ 12636838708417266 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 6584083614375689183119) ^ 21882966 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_7138431302142690111943 : Nat.Prime 7138431302142690111943 := by
  apply lucas_primality 7138431302142690111943 (5 : ZMod 7138431302142690111943)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (29, 1), (3593, 1), (223885590465631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (29, 1), (3593, 1), (223885590465631, 1)] : List FactorBlock).map factorBlockValue).prod) = 7138431302142690111943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_17
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_3593
      · exact prime_sixtySixBL_223885590465631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7138431302142690111943) ^ 3569215651071345055971 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7138431302142690111943) ^ 2379477100714230037314 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7138431302142690111943) ^ 419907723655452359526 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7138431302142690111943) ^ 246152803522161727998 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7138431302142690111943) ^ 1986760729792009494 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7138431302142690111943) ^ 31884282 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_11302909677208028749447 : Nat.Prime 11302909677208028749447 := by
  apply lucas_primality 11302909677208028749447 (3 : ZMod 11302909677208028749447)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (20113, 1), (843799326389087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (20113, 1), (843799326389087, 1)] : List FactorBlock).map factorBlockValue).prod) = 11302909677208028749447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_37
      · exact prime_sixtySixBL_20113
      · exact prime_sixtySixBL_843799326389087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11302909677208028749447) ^ 5651454838604014374723 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11302909677208028749447) ^ 3767636559069342916482 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11302909677208028749447) ^ 305484045329946722958 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11302909677208028749447) ^ 561970351375131942 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 11302909677208028749447) ^ 13395258 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_13037843241472521988123 : Nat.Prime 13037843241472521988123 := by
  apply lucas_primality 13037843241472521988123 (2 : ZMod 13037843241472521988123)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7353497, 1), (295502109211271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7353497, 1), (295502109211271, 1)] : List FactorBlock).map factorBlockValue).prod) = 13037843241472521988123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7353497
      · exact prime_sixtySixBL_295502109211271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13037843241472521988123) ^ 6518921620736260994061 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13037843241472521988123) ^ 4345947747157507329374 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13037843241472521988123) ^ 1773012655267626 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13037843241472521988123) ^ 44120982 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_23067994706658761108567 : Nat.Prime 23067994706658761108567 := by
  apply lucas_primality 23067994706658761108567 (5 : ZMod 23067994706658761108567)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (2215547, 1), (34476401734039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (2215547, 1), (34476401734039, 1)] : List FactorBlock).map factorBlockValue).prod) = 23067994706658761108567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_151
      · exact prime_sixtySixBL_2215547
      · exact prime_sixtySixBL_34476401734039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23067994706658761108567) ^ 11533997353329380554283 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23067994706658761108567) ^ 152768176865289808666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23067994706658761108567) ^ 10411873323679778 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 23067994706658761108567) ^ 669095194 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_24348340682114590995703 : Nat.Prime 24348340682114590995703 := by
  apply lucas_primality 24348340682114590995703 (3 : ZMod 24348340682114590995703)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4058056780352431832617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4058056780352431832617, 1)] : List FactorBlock).map factorBlockValue).prod) = 24348340682114590995703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_4058056780352431832617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24348340682114590995703) ^ 12174170341057295497851 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24348340682114590995703) ^ 8116113560704863665234 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24348340682114590995703) ^ 6 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_45307050324453195870349 : Nat.Prime 45307050324453195870349 := by
  apply lucas_primality 45307050324453195870349 (2 : ZMod 45307050324453195870349)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (311, 1), (1348905868895236271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (311, 1), (1348905868895236271, 1)] : List FactorBlock).map factorBlockValue).prod) = 45307050324453195870349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_311
      · exact prime_sixtySixBL_1348905868895236271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45307050324453195870349) ^ 22653525162226597935174 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 45307050324453195870349) ^ 15102350108151065290116 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 45307050324453195870349) ^ 145681833840685517268 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 45307050324453195870349) ^ 33588 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_53885845659613710576919 : Nat.Prime 53885845659613710576919 := by
  apply lucas_primality 53885845659613710576919 (6 : ZMod 53885845659613710576919)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (137, 1), (167, 1), (8209, 1), (1652459, 1), (4133971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (137, 1), (167, 1), (8209, 1), (1652459, 1), (4133971, 1)] : List FactorBlock).map factorBlockValue).prod) = 53885845659613710576919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_137
      · exact prime_sixtySixBL_167
      · exact prime_sixtySixBL_8209
      · exact prime_sixtySixBL_1652459
      · exact prime_sixtySixBL_4133971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 53885845659613710576919) ^ 26942922829806855288459 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 17961948553204570192306 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 7697977951373387225274 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 393327340581121975014 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 322669734488704853754 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 6564239939044184502 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 32609490256408002 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (6 : ZMod 53885845659613710576919) ^ 13034887196744658 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_146090044092687545974219 : Nat.Prime 146090044092687545974219 := by
  apply lucas_primality 146090044092687545974219 (3 : ZMod 146090044092687545974219)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24348340682114590995703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24348340682114590995703, 1)] : List FactorBlock).map factorBlockValue).prod) = 146090044092687545974219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_24348340682114590995703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146090044092687545974219) ^ 73045022046343772987109 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146090044092687545974219) ^ 48696681364229181991406 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 146090044092687545974219) ^ 6 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_200620696585822199397209 : Nat.Prime 200620696585822199397209 := by
  apply lucas_primality 200620696585822199397209 (3 : ZMod 200620696585822199397209)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (227, 1), (389, 1), (283994734870024517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (227, 1), (389, 1), (283994734870024517, 1)] : List FactorBlock).map factorBlockValue).prod) = 200620696585822199397209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_227
      · exact prime_sixtySixBL_389
      · exact prime_sixtySixBL_283994734870024517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 200620696585822199397209) ^ 100310348292911099698604 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 200620696585822199397209) ^ 883791614915516296904 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 200620696585822199397209) ^ 515734438523964522872 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 200620696585822199397209) ^ 706424 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_381786937815766083059741 : Nat.Prime 381786937815766083059741 := by
  apply lucas_primality 381786937815766083059741 (2 : ZMod 381786937815766083059741)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (55661, 1), (14911187437295729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (55661, 1), (14911187437295729, 1)] : List FactorBlock).map factorBlockValue).prod) = 381786937815766083059741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_55661
      · exact prime_sixtySixBL_14911187437295729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381786937815766083059741) ^ 190893468907883041529870 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381786937815766083059741) ^ 76357387563153216611948 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381786937815766083059741) ^ 16599432078946351437380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381786937815766083059741) ^ 6859146221156035340 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 381786937815766083059741) ^ 25604060 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_978550468407151643538373 : Nat.Prime 978550468407151643538373 := by
  apply lucas_primality 978550468407151643538373 (2 : ZMod 978550468407151643538373)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 2), (59566013416554154099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 2), (59566013416554154099, 1)] : List FactorBlock).map factorBlockValue).prod) = 978550468407151643538373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_37
      · exact prime_sixtySixBL_59566013416554154099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 978550468407151643538373) ^ 489275234203575821769186 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 978550468407151643538373) ^ 326183489469050547846124 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 978550468407151643538373) ^ 26447309956950044419956 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 978550468407151643538373) ^ 16428 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_4957093853680596661949677 : Nat.Prime 4957093853680596661949677 := by
  apply lucas_primality 4957093853680596661949677 (2 : ZMod 4957093853680596661949677)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (112543, 1), (924557, 1), (17489116049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (112543, 1), (924557, 1), (17489116049, 1)] : List FactorBlock).map factorBlockValue).prod) = 4957093853680596661949677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_227
      · exact prime_sixtySixBL_112543
      · exact prime_sixtySixBL_924557
      · exact prime_sixtySixBL_17489116049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4957093853680596661949677) ^ 2478546926840298330974838 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4957093853680596661949677) ^ 1652364617893532220649892 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4957093853680596661949677) ^ 21837417857623773841188 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4957093853680596661949677) ^ 44046221032677258132 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4957093853680596661949677) ^ 5361588148357101468 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4957093853680596661949677) ^ 283438787860524 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5672405812066463510886149 : Nat.Prime 5672405812066463510886149 := by
  apply lucas_primality 5672405812066463510886149 (2 : ZMod 5672405812066463510886149)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19676372977, 1), (72071283395281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19676372977, 1), (72071283395281, 1)] : List FactorBlock).map factorBlockValue).prod) = 5672405812066463510886149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_19676372977
      · exact prime_sixtySixBL_72071283395281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5672405812066463510886149) ^ 2836202906033231755443074 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5672405812066463510886149) ^ 288285133581124 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5672405812066463510886149) ^ 78705491908 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5811828865692408167417687 : Nat.Prime 5811828865692408167417687 := by
  apply lucas_primality 5811828865692408167417687 (5 : ZMod 5811828865692408167417687)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (154682441, 1), (307972522376143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (154682441, 1), (307972522376143, 1)] : List FactorBlock).map factorBlockValue).prod) = 5811828865692408167417687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_61
      · exact prime_sixtySixBL_154682441
      · exact prime_sixtySixBL_307972522376143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5811828865692408167417687) ^ 2905914432846204083708843 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5811828865692408167417687) ^ 95275883044137838810126 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5811828865692408167417687) ^ 37572647729889446 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 5811828865692408167417687) ^ 18871257802 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_5843601763707501838968761 : Nat.Prime 5843601763707501838968761 := by
  apply lucas_primality 5843601763707501838968761 (3 : ZMod 5843601763707501838968761)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (146090044092687545974219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (146090044092687545974219, 1)] : List FactorBlock).map factorBlockValue).prod) = 5843601763707501838968761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_146090044092687545974219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5843601763707501838968761) ^ 2921800881853750919484380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5843601763707501838968761) ^ 1168720352741500367793752 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5843601763707501838968761) ^ 40 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_20841243149248470100360541 : Nat.Prime 20841243149248470100360541 := by
  apply lucas_primality 20841243149248470100360541 (2 : ZMod 20841243149248470100360541)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (45307050324453195870349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (45307050324453195870349, 1)] : List FactorBlock).map factorBlockValue).prod) = 20841243149248470100360541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_23
      · exact prime_sixtySixBL_45307050324453195870349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20841243149248470100360541) ^ 10420621574624235050180270 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20841243149248470100360541) ^ 4168248629849694020072108 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20841243149248470100360541) ^ 906141006489063917406980 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 20841243149248470100360541) ^ 460 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_23964869272354506159628337 : Nat.Prime 23964869272354506159628337 := by
  apply lucas_primality 23964869272354506159628337 (3 : ZMod 23964869272354506159628337)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (12527, 1), (119566083621150844973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (12527, 1), (119566083621150844973, 1)] : List FactorBlock).map factorBlockValue).prod) = 23964869272354506159628337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_12527
      · exact prime_sixtySixBL_119566083621150844973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23964869272354506159628337) ^ 11982434636177253079814168 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23964869272354506159628337) ^ 1913057337938413519568 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 23964869272354506159628337) ^ 200432 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_29356514052214549306151191 : Nat.Prime 29356514052214549306151191 := by
  apply lucas_primality 29356514052214549306151191 (3 : ZMod 29356514052214549306151191)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (978550468407151643538373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (978550468407151643538373, 1)] : List FactorBlock).map factorBlockValue).prod) = 29356514052214549306151191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_978550468407151643538373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29356514052214549306151191) ^ 14678257026107274653075595 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 29356514052214549306151191) ^ 9785504684071516435383730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 29356514052214549306151191) ^ 5871302810442909861230238 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 29356514052214549306151191) ^ 30 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_36175064603980654638734291 : Nat.Prime 36175064603980654638734291 := by
  apply lucas_primality 36175064603980654638734291 (2 : ZMod 36175064603980654638734291)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3673, 1), (984891494799364406173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3673, 1), (984891494799364406173, 1)] : List FactorBlock).map factorBlockValue).prod) = 36175064603980654638734291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_3673
      · exact prime_sixtySixBL_984891494799364406173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36175064603980654638734291) ^ 18087532301990327319367145 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36175064603980654638734291) ^ 7235012920796130927746858 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36175064603980654638734291) ^ 9848914947993644061730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 36175064603980654638734291) ^ 36730 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_159896750718824327983093987 : Nat.Prime 159896750718824327983093987 := by
  apply lucas_primality 159896750718824327983093987 (3 : ZMod 159896750718824327983093987)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7632643163, 1), (3491511116663137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7632643163, 1), (3491511116663137, 1)] : List FactorBlock).map factorBlockValue).prod) = 159896750718824327983093987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7632643163
      · exact prime_sixtySixBL_3491511116663137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 159896750718824327983093987) ^ 79948375359412163991546993 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 159896750718824327983093987) ^ 53298916906274775994364662 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 159896750718824327983093987) ^ 20949066699978822 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 159896750718824327983093987) ^ 45795858978 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_191718954178836049277026697 : Nat.Prime 191718954178836049277026697 := by
  apply lucas_primality 191718954178836049277026697 (3 : ZMod 191718954178836049277026697)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23964869272354506159628337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23964869272354506159628337, 1)] : List FactorBlock).map factorBlockValue).prod) = 191718954178836049277026697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_23964869272354506159628337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 191718954178836049277026697) ^ 95859477089418024638513348 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 191718954178836049277026697) ^ 8 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_193142609779173940732054123 : Nat.Prime 193142609779173940732054123 := by
  apply lucas_primality 193142609779173940732054123 (2 : ZMod 193142609779173940732054123)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (823, 1), (13037843241472521988123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (823, 1), (13037843241472521988123, 1)] : List FactorBlock).map factorBlockValue).prod) = 193142609779173940732054123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_823
      · exact prime_sixtySixBL_13037843241472521988123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193142609779173940732054123) ^ 96571304889586970366027061 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 193142609779173940732054123) ^ 64380869926391313577351374 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 193142609779173940732054123) ^ 234681178346505395786214 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 193142609779173940732054123) ^ 14814 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_376954658699450589641303699 : Nat.Prime 376954658699450589641303699 := by
  apply lucas_primality 376954658699450589641303699 (2 : ZMod 376954658699450589641303699)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7460699, 1), (25262690446260503851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7460699, 1), (25262690446260503851, 1)] : List FactorBlock).map factorBlockValue).prod) = 376954658699450589641303699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_7460699
      · exact prime_sixtySixBL_25262690446260503851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 376954658699450589641303699) ^ 188477329349725294820651849 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 376954658699450589641303699) ^ 50525380892521007702 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 376954658699450589641303699) ^ 14921398 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_750284753372944923612979477 : Nat.Prime 750284753372944923612979477 := by
  apply lucas_primality 750284753372944923612979477 (2 : ZMod 750284753372944923612979477)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (20841243149248470100360541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (20841243149248470100360541, 1)] : List FactorBlock).map factorBlockValue).prod) = 750284753372944923612979477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_20841243149248470100360541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 750284753372944923612979477) ^ 375142376686472461806489738 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 750284753372944923612979477) ^ 250094917790981641204326492 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 750284753372944923612979477) ^ 36 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_780296143507862720557498657 : Nat.Prime 780296143507862720557498657 := by
  apply lucas_primality 780296143507862720557498657 (7 : ZMod 780296143507862720557498657)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) = 780296143507862720557498657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_109
      · exact prime_sixtySixBL_2377
      · exact prime_sixtySixBL_31371302305376460727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 780296143507862720557498657) ^ 390148071753931360278749328 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 780296143507862720557498657) ^ 260098714502620906852499552 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 780296143507862720557498657) ^ 7158680215668465326215584 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 780296143507862720557498657) ^ 328269307323459285047328 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 780296143507862720557498657) ^ 24872928 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_812808482820690333914061101 : Nat.Prime 812808482820690333914061101 := by
  apply lucas_primality 812808482820690333914061101 (10 : ZMod 812808482820690333914061101)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) = 812808482820690333914061101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_109
      · exact prime_sixtySixBL_2377
      · exact prime_sixtySixBL_31371302305376460727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 812808482820690333914061101) ^ 406404241410345166957030550 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 812808482820690333914061101) ^ 162561696564138066782812220 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 812808482820690333914061101) ^ 7456958557987984714807900 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 812808482820690333914061101) ^ 341947195128603421924300 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (10 : ZMod 812808482820690333914061101) ^ 25909300 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_1418720260923386764649997557 : Nat.Prime 1418720260923386764649997557 := by
  apply lucas_primality 1418720260923386764649997557 (2 : ZMod 1418720260923386764649997557)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (929, 1), (381786937815766083059741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (929, 1), (381786937815766083059741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1418720260923386764649997557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_929
      · exact prime_sixtySixBL_381786937815766083059741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1418720260923386764649997557) ^ 709360130461693382324998778 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418720260923386764649997557) ^ 1527147751263064332238964 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418720260923386764649997557) ^ 3716 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2438425448462071001742183301 : Nat.Prime 2438425448462071001742183301 := by
  apply lucas_primality 2438425448462071001742183301 (7 : ZMod 2438425448462071001742183301)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2438425448462071001742183301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_109
      · exact prime_sixtySixBL_2377
      · exact prime_sixtySixBL_31371302305376460727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2438425448462071001742183301) ^ 1219212724231035500871091650 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2438425448462071001742183301) ^ 812808482820690333914061100 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2438425448462071001742183301) ^ 487685089692414200348436660 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2438425448462071001742183301) ^ 22370875673963954144423700 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2438425448462071001742183301) ^ 1025841585385810265772900 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2438425448462071001742183301) ^ 77727900 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_2517084333896331356637092441 : Nat.Prime 2517084333896331356637092441 := by
  apply lucas_primality 2517084333896331356637092441 (3 : ZMod 2517084333896331356637092441)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37087, 1), (1696743019047328819153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37087, 1), (1696743019047328819153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2517084333896331356637092441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_37087
      · exact prime_sixtySixBL_1696743019047328819153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2517084333896331356637092441) ^ 1258542166948165678318546220 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517084333896331356637092441) ^ 503416866779266271327418488 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517084333896331356637092441) ^ 67869720761893152766120 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517084333896331356637092441) ^ 1483480 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_3251233931282761335656244403 : Nat.Prime 3251233931282761335656244403 := by
  apply lucas_primality 3251233931282761335656244403 (2 : ZMod 3251233931282761335656244403)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3251233931282761335656244403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_887
      · exact prime_sixtySixBL_20709473
      · exact prime_sixtySixBL_4214113817456531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3251233931282761335656244403) ^ 1625616965641380667828122201 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3251233931282761335656244403) ^ 1083744643760920445218748134 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3251233931282761335656244403) ^ 464461990183251619379463486 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3251233931282761335656244403) ^ 3665427205504804211562846 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3251233931282761335656244403) ^ 156992596155525605874 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3251233931282761335656244403) ^ 771510707142 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_6002278026983559388903835821 : Nat.Prime 6002278026983559388903835821 := by
  apply lucas_primality 6002278026983559388903835821 (7 : ZMod 6002278026983559388903835821)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (397, 1), (5717, 1), (285147727, 1), (154573928539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (397, 1), (5717, 1), (285147727, 1), (154573928539, 1)] : List FactorBlock).map factorBlockValue).prod) = 6002278026983559388903835821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_397
      · exact prime_sixtySixBL_5717
      · exact prime_sixtySixBL_285147727
      · exact prime_sixtySixBL_154573928539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6002278026983559388903835821) ^ 3001139013491779694451917910 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 2000759342327853129634611940 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 1200455605396711877780767164 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 15119088229177731458196060 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 1049899952244806609918460 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 21049713740076768660 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (7 : ZMod 6002278026983559388903835821) ^ 38831115206269380 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_11147087764398038865107123663 : Nat.Prime 11147087764398038865107123663 := by
  apply lucas_primality 11147087764398038865107123663 (5 : ZMod 11147087764398038865107123663)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (353, 1), (178952422711, 1), (522074441353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (353, 1), (178952422711, 1), (522074441353, 1)] : List FactorBlock).map factorBlockValue).prod) = 11147087764398038865107123663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_353
      · exact prime_sixtySixBL_178952422711
      · exact prime_sixtySixBL_522074441353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11147087764398038865107123663) ^ 5573543882199019432553561831 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11147087764398038865107123663) ^ 857468289569079912700547974 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11147087764398038865107123663) ^ 31578152307076597351578254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11147087764398038865107123663) ^ 62290789895591842 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 11147087764398038865107123663) ^ 21351529363340254 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_15605922870157254411149973133 : Nat.Prime 15605922870157254411149973133 := by
  apply lucas_primality 15605922870157254411149973133 (2 : ZMod 15605922870157254411149973133)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (397, 1), (5717, 1), (285147727, 1), (154573928539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (397, 1), (5717, 1), (285147727, 1), (154573928539, 1)] : List FactorBlock).map factorBlockValue).prod) = 15605922870157254411149973133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_13
      · exact prime_sixtySixBL_397
      · exact prime_sixtySixBL_5717
      · exact prime_sixtySixBL_285147727
      · exact prime_sixtySixBL_154573928539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15605922870157254411149973133) ^ 7802961435078627205574986566 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 5201974290052418137049991044 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 1200455605396711877780767164 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 39309629395862101791309756 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 2729739875836497185787996 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 54729255724199598516 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15605922870157254411149973133) ^ 100960899536300388 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_19507403587696568013937466413 : Nat.Prime 19507403587696568013937466413 := by
  apply lucas_primality 19507403587696568013937466413 (2 : ZMod 19507403587696568013937466413)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) = 19507403587696568013937466413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_887
      · exact prime_sixtySixBL_20709473
      · exact prime_sixtySixBL_4214113817456531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19507403587696568013937466413) ^ 9753701793848284006968733206 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19507403587696568013937466413) ^ 6502467862565522671312488804 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19507403587696568013937466413) ^ 2786771941099509716276780916 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19507403587696568013937466413) ^ 21992563233028825269377076 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19507403587696568013937466413) ^ 941955576933153635244 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 19507403587696568013937466413) ^ 4629064242852 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_78029614350786272055749865611 : Nat.Prime 78029614350786272055749865611 := by
  apply lucas_primality 78029614350786272055749865611 (2 : ZMod 78029614350786272055749865611)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (499, 1), (10973, 1), (49140043632762007267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (499, 1), (10973, 1), (49140043632762007267, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_5
      · exact prime_sixtySixBL_29
      · exact prime_sixtySixBL_499
      · exact prime_sixtySixBL_10973
      · exact prime_sixtySixBL_49140043632762007267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78029614350786272055749865611) ^ 39014807175393136027874932805 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865611) ^ 15605922870157254411149973122 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865611) ^ 2690676356923664553646547090 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865611) ^ 156371972646866276664829390 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865611) ^ 7111055714096990071607570 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865611) ^ 1587902830 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_78029614350786272055749865637 : Nat.Prime 78029614350786272055749865637 := by
  apply lucas_primality 78029614350786272055749865637 (5 : ZMod 78029614350786272055749865637)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (129552509, 1), (1067909692544708561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (129552509, 1), (1067909692544708561, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_47
      · exact prime_sixtySixBL_129552509
      · exact prime_sixtySixBL_1067909692544708561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 78029614350786272055749865637) ^ 39014807175393136027874932818 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 78029614350786272055749865637) ^ 26009871450262090685249955212 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 78029614350786272055749865637) ^ 1660204560655027065015954588 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 78029614350786272055749865637) ^ 602301066595215628404 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (5 : ZMod 78029614350786272055749865637) ^ 73067615076 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_78029614350786272055749865649 : Nat.Prime 78029614350786272055749865649 := by
  apply lucas_primality 78029614350786272055749865649 (13 : ZMod 78029614350786272055749865649)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_3
      · exact prime_sixtySixBL_7
      · exact prime_sixtySixBL_887
      · exact prime_sixtySixBL_20709473
      · exact prime_sixtySixBL_4214113817456531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 78029614350786272055749865649) ^ 39014807175393136027874932824 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 78029614350786272055749865649) ^ 26009871450262090685249955216 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 78029614350786272055749865649) ^ 11147087764398038865107123664 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 78029614350786272055749865649) ^ 87970252932115301077508304 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 78029614350786272055749865649) ^ 3767822307732614540976 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (13 : ZMod 78029614350786272055749865649) ^ 18516256971408 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem prime_sixtySixBL_78029614350786272055749865659 : Nat.Prime 78029614350786272055749865659 := by
  apply lucas_primality 78029614350786272055749865659 (2 : ZMod 78029614350786272055749865659)
  · rw [← sixtySixBLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (54541, 1), (3165661, 1), (12754033, 1), (17717173013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (54541, 1), (3165661, 1), (12754033, 1), (17717173013, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtySixBL_2
      · exact prime_sixtySixBL_54541
      · exact prime_sixtySixBL_3165661
      · exact prime_sixtySixBL_12754033
      · exact prime_sixtySixBL_17717173013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78029614350786272055749865659) ^ 39014807175393136027874932829 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865659) ^ 1430659766978718249679138 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865659) ^ 24648758774482255698178 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865659) ^ 6118034534706494177626 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide
    · change (2 : ZMod 78029614350786272055749865659) ^ 4404179735307203666 ≠ 1
      rw [← sixtySixBLFastPow_eq_pow]
      decide

private theorem phi_sixtySixBL_78029614350786272055749865600 : Nat.totient 78029614350786272055749865600 = 20608325483463789654982164480 := by
  rw [← show ((([(2, 7), (3, 1), (5, 2), (109, 1), (2377, 1), (31371302305376460727, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_109, prime_sixtySixBL_2377, prime_sixtySixBL_31371302305376460727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865601 : Nat.totient 78029614350786272055749865601 = 74475817648948488437136798480 := by
  rw [← show ((([(23, 1), (463, 1), (43774391, 1), (167390389785835039, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_23, prime_sixtySixBL_463, prime_sixtySixBL_43774391, prime_sixtySixBL_167390389785835039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865602 : Nat.totient 78029614350786272055749865602 = 35102319254773103912982036480 := by
  rw [← show ((([(2, 1), (11, 1), (97, 1), (930689, 1), (39288049153302341827, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_11, prime_sixtySixBL_97, prime_sixtySixBL_930689, prime_sixtySixBL_39288049153302341827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865603 : Nat.totient 78029614350786272055749865603 = 50532139319004944712413482752 := by
  rw [← show ((([(3, 3), (67, 1), (79, 1), (809, 1), (674909095062884289397, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_67, prime_sixtySixBL_79, prime_sixtySixBL_809, prime_sixtySixBL_674909095062884289397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865604 : Nat.totient 78029614350786272055749865604 = 38278269692295860855131137920 := by
  rw [← show ((([(2, 2), (53, 1), (93581, 1), (15982992863, 1), (246080846639, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_53, prime_sixtySixBL_93581, prime_sixtySixBL_15982992863, prime_sixtySixBL_246080846639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865605 : Nat.totient 78029614350786272055749865605 = 60736564469160966426899078592 := by
  rw [← show ((([(5, 1), (37, 1), (282897899, 1), (1490932596828650567, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_37, prime_sixtySixBL_282897899, prime_sixtySixBL_1490932596828650567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865606 : Nat.totient 78029614350786272055749865606 = 20507999318326247362994822400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (19, 1), (41, 1), (211, 1), (11302909677208028749447, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_7, prime_sixtySixBL_19, prime_sixtySixBL_41, prime_sixtySixBL_211, prime_sixtySixBL_11302909677208028749447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865607 : Nat.totient 78029614350786272055749865607 = 77585556272704037903626017408 := by
  rw [← show ((([(197, 1), (1619, 1), (4527517, 1), (54036386069033197, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_197, prime_sixtySixBL_1619, prime_sixtySixBL_4527517, prime_sixtySixBL_54036386069033197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865608 : Nat.totient 78029614350786272055749865608 = 36013668161901356333423014848 := by
  rw [← show ((([(2, 3), (13, 1), (750284753372944923612979477, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_13, prime_sixtySixBL_750284753372944923612979477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865609 : Nat.totient 78029614350786272055749865609 = 50286894300627026792828500800 := by
  rw [← show ((([(3, 1), (31, 1), (919, 1), (3694711, 1), (247104427507920557, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_31, prime_sixtySixBL_919, prime_sixtySixBL_3694711, prime_sixtySixBL_247104427507920557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865610 : Nat.totient 78029614350786272055749865610 = 30072442428207764745869060352 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (499, 1), (10973, 1), (49140043632762007267, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_29, prime_sixtySixBL_499, prime_sixtySixBL_10973, prime_sixtySixBL_49140043632762007267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865611 : Nat.totient 78029614350786272055749865611 = 78029614350786272055749865610 := by
  rw [← show ((([(78029614350786272055749865611, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_78029614350786272055749865611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865612 : Nat.totient 78029614350786272055749865612 = 25938932861934582933583134720 := by
  rw [← show ((([(2, 2), (3, 2), (431, 1), (2473, 1), (267637, 1), (38534009, 1), (197181073, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_431, prime_sixtySixBL_2473, prime_sixtySixBL_267637, prime_sixtySixBL_38534009, prime_sixtySixBL_197181073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865613 : Nat.totient 78029614350786272055749865613 = 57225691196821701851212823040 := by
  rw [← show ((([(7, 2), (11, 1), (17, 1), (686112379003, 1), (12411564223717, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_7, prime_sixtySixBL_11, prime_sixtySixBL_17, prime_sixtySixBL_686112379003, prime_sixtySixBL_12411564223717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865614 : Nat.totient 78029614350786272055749865614 = 39014787078162318467737024800 := by
  rw [← show ((([(2, 1), (1945061, 1), (1004729927, 1), (19963969625581, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_1945061, prime_sixtySixBL_1004729927, prime_sixtySixBL_19963969625581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865615 : Nat.totient 78029614350786272055749865615 = 41615700524496083220680358144 := by
  rw [← show ((([(3, 1), (5, 1), (644227, 1), (1425299, 1), (5665305037057417, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_644227, prime_sixtySixBL_1425299, prime_sixtySixBL_5665305037057417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865616 : Nat.totient 78029614350786272055749865616 = 38865386682966865454628019200 := by
  rw [← show ((([(2, 4), (307, 1), (1741, 1), (75222672983, 1), (121297980281, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_307, prime_sixtySixBL_1741, prime_sixtySixBL_75222672983, prime_sixtySixBL_121297980281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865617 : Nat.totient 78029614350786272055749865617 = 77965546929849541411984255248 := by
  rw [← show ((([(1453, 1), (7523, 1), (7138431302142690111943, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_1453, prime_sixtySixBL_7523, prime_sixtySixBL_7138431302142690111943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865618 : Nat.totient 78029614350786272055749865618 = 25559748891524315746996309568 := by
  rw [← show ((([(2, 1), (3, 1), (59, 1), (2903, 1), (54443, 1), (1394656047301929773, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_59, prime_sixtySixBL_2903, prime_sixtySixBL_54443, prime_sixtySixBL_1394656047301929773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865619 : Nat.totient 78029614350786272055749865619 = 77926183141164105647828427840 := by
  rw [← show ((([(761, 1), (87013, 1), (1178394376655308669583, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_761, prime_sixtySixBL_87013, prime_sixtySixBL_1178394376655308669583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865620 : Nat.totient 78029614350786272055749865620 = 26753010634116110124500874240 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (60915790241, 1), (9149588079131063, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_7, prime_sixtySixBL_60915790241, prime_sixtySixBL_9149588079131063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865621 : Nat.totient 78029614350786272055749865621 = 48012183352292019745878725760 := by
  rw [← show ((([(3, 2), (13, 1), (7949, 1), (635710067, 1), (131978142858311, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_13, prime_sixtySixBL_7949, prime_sixtySixBL_635710067, prime_sixtySixBL_131978142858311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865622 : Nat.totient 78029614350786272055749865622 = 39008683581951025760082693120 := by
  rw [← show ((([(2, 1), (7393, 1), (46093, 1), (6951088349, 1), (16471038211, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_7393, prime_sixtySixBL_46093, prime_sixtySixBL_6951088349, prime_sixtySixBL_16471038211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865623 : Nat.totient 78029614350786272055749865623 = 76596841120285649709345600000 := by
  rw [← show ((([(107, 1), (151, 1), (401, 1), (701621, 1), (17165315239064359, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_107, prime_sixtySixBL_151, prime_sixtySixBL_401, prime_sixtySixBL_701621, prime_sixtySixBL_17165315239064359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865624 : Nat.totient 78029614350786272055749865624 = 22182447717171988501432320000 := by
  rw [← show ((([(2, 3), (3, 1), (11, 2), (23, 1), (89, 1), (163, 1), (521, 1), (26171, 1), (5906080480031, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_11, prime_sixtySixBL_23, prime_sixtySixBL_89, prime_sixtySixBL_163, prime_sixtySixBL_521, prime_sixtySixBL_26171, prime_sixtySixBL_5906080480031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865625 : Nat.totient 78029614350786272055749865625 = 59069702981380952900780280000 := by
  rw [← show ((([(5, 5), (19, 1), (863, 1), (12541687, 1), (121419680053663, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_19, prime_sixtySixBL_863, prime_sixtySixBL_12541687, prime_sixtySixBL_121419680053663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865626 : Nat.totient 78029614350786272055749865626 = 38700814352734566936342507600 := by
  rw [← show ((([(2, 1), (127, 1), (5701, 1), (53885845659613710576919, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_127, prime_sixtySixBL_5701, prime_sixtySixBL_53885845659613710576919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865627 : Nat.totient 78029614350786272055749865627 = 43551348832603743977003276160 := by
  rw [← show ((([(3, 1), (7, 1), (43, 1), (682411, 1), (7504841413, 1), (16872683963, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_7, prime_sixtySixBL_43, prime_sixtySixBL_682411, prime_sixtySixBL_7504841413, prime_sixtySixBL_16872683963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865628 : Nat.totient 78029614350786272055749865628 = 38962231211424571633346641920 := by
  rw [← show ((([(2, 2), (797, 1), (10753, 1), (235760431, 1), (9654740052317, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_797, prime_sixtySixBL_10753, prime_sixtySixBL_235760431, prime_sixtySixBL_9654740052317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865629 : Nat.totient 78029614350786272055749865629 = 77350892177069084776092054912 := by
  rw [← show ((([(167, 1), (367, 1), (563113, 1), (2260900092040934797, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_167, prime_sixtySixBL_367, prime_sixtySixBL_563113, prime_sixtySixBL_2260900092040934797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865630 : Nat.totient 78029614350786272055749865630 = 19583882771238953080798040064 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (17, 1), (958193, 1), (5913880251878086483, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_17, prime_sixtySixBL_958193, prime_sixtySixBL_5913880251878086483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865631 : Nat.totient 78029614350786272055749865631 = 76930144812105290094738322680 := by
  rw [← show ((([(71, 1), (166919, 1), (6584083614375689183119, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_71, prime_sixtySixBL_166919, prime_sixtySixBL_6584083614375689183119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865632 : Nat.totient 78029614350786272055749865632 = 39014807175393136027874932800 := by
  rw [← show ((([(2, 5), (2438425448462071001742183301, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_2438425448462071001742183301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865633 : Nat.totient 78029614350786272055749865633 = 52008055696996766366821964000 := by
  rw [← show ((([(3, 1), (4451, 1), (5843601763707501838968761, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_4451, prime_sixtySixBL_5843601763707501838968761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865634 : Nat.totient 78029614350786272055749865634 = 30781411233251696018520330240 := by
  rw [← show ((([(2, 1), (7, 1), (13, 2), (353, 1), (178952422711, 1), (522074441353, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_7, prime_sixtySixBL_13, prime_sixtySixBL_353, prime_sixtySixBL_178952422711, prime_sixtySixBL_522074441353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865635 : Nat.totient 78029614350786272055749865635 = 56748810436935470585999902240 := by
  rw [← show ((([(5, 1), (11, 1), (1418720260923386764649997557, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_11, prime_sixtySixBL_1418720260923386764649997557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865636 : Nat.totient 78029614350786272055749865636 = 25456469733548364878180600320 := by
  rw [← show ((([(2, 2), (3, 1), (47, 1), (129552509, 1), (1067909692544708561, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_47, prime_sixtySixBL_129552509, prime_sixtySixBL_1067909692544708561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865637 : Nat.totient 78029614350786272055749865637 = 78029614350786272055749865636 := by
  rw [← show ((([(78029614350786272055749865637, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_78029614350786272055749865637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865638 : Nat.totient 78029614350786272055749865638 = 39014807175246210976540361880 := by
  rw [← show ((([(2, 1), (265542719461, 1), (146924785791851479, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_265542719461, prime_sixtySixBL_146924785791851479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865639 : Nat.totient 78029614350786272055749865639 = 49598938308206265999762654528 := by
  rw [← show ((([(3, 2), (29, 1), (83, 1), (2267, 1), (1588873569220959446459, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_29, prime_sixtySixBL_83, prime_sixtySixBL_2267, prime_sixtySixBL_1588873569220959446459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865640 : Nat.totient 78029614350786272055749865640 = 30204197570106833561794114560 := by
  rw [← show ((([(2, 3), (5, 1), (31, 1), (37087, 1), (1696743019047328819153, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_31, prime_sixtySixBL_37087, prime_sixtySixBL_1696743019047328819153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865641 : Nat.totient 78029614350786272055749865641 = 66882526586388233190642741972 := by
  rw [← show ((([(7, 1), (11147087764398038865107123663, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_7, prime_sixtySixBL_11147087764398038865107123663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865642 : Nat.totient 78029614350786272055749865642 = 24958273321211550842990790144 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (73, 1), (12743, 1), (377843488961294990149, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_37, prime_sixtySixBL_73, prime_sixtySixBL_12743, prime_sixtySixBL_377843488961294990149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865643 : Nat.totient 78029614350786272055749865643 = 78029614350785367046519329880 := by
  rw [← show ((([(96511901173973, 1), (808497329361791, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_96511901173973, prime_sixtySixBL_808497329361791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865644 : Nat.totient 78029614350786272055749865644 = 36757189662190683550542239040 := by
  rw [← show ((([(2, 2), (19, 1), (181, 1), (5672405812066463510886149, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_19, prime_sixtySixBL_181, prime_sixtySixBL_5672405812066463510886149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865645 : Nat.totient 78029614350786272055749865645 = 41615793737546364029093016704 := by
  rw [← show ((([(3, 1), (5, 1), (71397707, 1), (72859122633341966249, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_71397707, prime_sixtySixBL_72859122633341966249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865646 : Nat.totient 78029614350786272055749865646 = 35463917883590549764377120000 := by
  rw [← show ((([(2, 1), (11, 1), (8681, 1), (21152011, 1), (29464571, 1), (655564213, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_11, prime_sixtySixBL_8681, prime_sixtySixBL_21152011, prime_sixtySixBL_29464571, prime_sixtySixBL_655564213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865647 : Nat.totient 78029614350786272055749865647 = 63243446203823694062917386240 := by
  rw [← show ((([(13, 1), (17, 2), (23, 1), (41, 1), (3547, 1), (307873, 1), (20168508413087, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_13, prime_sixtySixBL_17, prime_sixtySixBL_23, prime_sixtySixBL_41, prime_sixtySixBL_3547, prime_sixtySixBL_307873, prime_sixtySixBL_20168508413087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865648 : Nat.totient 78029614350786272055749865648 = 22269040095508473501335162880 := by
  rw [← show ((([(2, 4), (3, 2), (7, 1), (887, 1), (20709473, 1), (4214113817456531, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_7, prime_sixtySixBL_887, prime_sixtySixBL_20709473, prime_sixtySixBL_4214113817456531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865649 : Nat.totient 78029614350786272055749865649 = 78029614350786272055749865648 := by
  rw [← show ((([(78029614350786272055749865649, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_78029614350786272055749865649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865650 : Nat.totient 78029614350786272055749865650 = 31211798938996561608968856000 := by
  rw [← show ((([(2, 1), (5, 2), (666901, 1), (2340065897360665887613, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_666901, prime_sixtySixBL_2340065897360665887613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865651 : Nat.totient 78029614350786272055749865651 = 52019742833992879030680710760 := by
  rw [← show ((([(3, 1), (781883731, 1), (33265651169127716107, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_781883731, prime_sixtySixBL_33265651169127716107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865652 : Nat.totient 78029614350786272055749865652 = 39014807175393136027874932824 := by
  rw [← show ((([(2, 2), (19507403587696568013937466413, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_19507403587696568013937466413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865653 : Nat.totient 78029614350786272055749865653 = 77992758525037479115618644928 := by
  rw [← show ((([(2129, 1), (380459, 1), (96333188918580451823, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2129, prime_sixtySixBL_380459, prime_sixtySixBL_96333188918580451823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865654 : Nat.totient 78029614350786272055749865654 = 25811321709427341099872308800 := by
  rw [← show ((([(2, 1), (3, 1), (131, 1), (23383849, 1), (4245422492783404811, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_131, prime_sixtySixBL_23383849, prime_sixtySixBL_4245422492783404811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865655 : Nat.totient 78029614350786272055749865655 = 53506021268335959493495142400 := by
  rw [← show ((([(5, 1), (7, 1), (69073414301, 1), (32276058385712833, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_7, prime_sixtySixBL_69073414301, prime_sixtySixBL_32276058385712833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865656 : Nat.totient 78029614350786272055749865656 = 38375220172517838715942556640 := by
  rw [← show ((([(2, 3), (61, 1), (159896750718824327983093987, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_61, prime_sixtySixBL_159896750718824327983093987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865657 : Nat.totient 78029614350786272055749865657 = 46398398470450384755848967360 := by
  rw [← show ((([(3, 3), (11, 1), (53, 1), (4957093853680596661949677, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_11, prime_sixtySixBL_53, prime_sixtySixBL_4957093853680596661949677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865658 : Nat.totient 78029614350786272055749865658 = 39014076460193961717454617600 := by
  rw [← show ((([(2, 1), (54541, 1), (3165661, 1), (12754033, 1), (17717173013, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_54541, prime_sixtySixBL_3165661, prime_sixtySixBL_12754033, prime_sixtySixBL_17717173013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865659 : Nat.totient 78029614350786272055749865659 = 78029614350786272055749865658 := by
  rw [← show ((([(78029614350786272055749865659, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_78029614350786272055749865659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865660 : Nat.totient 78029614350786272055749865660 = 19155557319534892124986208256 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (13, 1), (397, 1), (5717, 1), (285147727, 1), (154573928539, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_13, prime_sixtySixBL_397, prime_sixtySixBL_5717, prime_sixtySixBL_285147727, prime_sixtySixBL_154573928539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865661 : Nat.totient 78029614350786272055749865661 = 77950150566977707065758655360 := by
  rw [← show ((([(1531, 1), (2749, 1), (594313, 1), (31195668726579163, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_1531, prime_sixtySixBL_2749, prime_sixtySixBL_594313, prime_sixtySixBL_31195668726579163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865662 : Nat.totient 78029614350786272055749865662 = 33197166480835035452289822432 := by
  rw [← show ((([(2, 1), (7, 2), (137, 1), (5811828865692408167417687, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_7, prime_sixtySixBL_137, prime_sixtySixBL_5811828865692408167417687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865663 : Nat.totient 78029614350786272055749865663 = 49226873913497243510657187840 := by
  rw [← show ((([(3, 1), (19, 1), (1553, 1), (3391, 1), (5653, 1), (2340769, 1), (19644809269, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_19, prime_sixtySixBL_1553, prime_sixtySixBL_3391, prime_sixtySixBL_5653, prime_sixtySixBL_2340769, prime_sixtySixBL_19644809269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865664 : Nat.totient 78029614350786272055749865664 = 36708007704727259917016641536 := by
  rw [← show ((([(2, 6), (17, 1), (3109, 1), (23067994706658761108567, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_17, prime_sixtySixBL_3109, prime_sixtySixBL_23067994706658761108567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865665 : Nat.totient 78029614350786272055749865665 = 62423691480629017644599892528 := by
  rw [← show ((([(5, 1), (15605922870157254411149973133, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_15605922870157254411149973133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865666 : Nat.totient 78029614350786272055749865666 = 26009871450261299721474691896 := by
  rw [← show ((([(2, 1), (3, 2), (62810357824639, 1), (69016938052583, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_62810357824639, prime_sixtySixBL_69016938052583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865667 : Nat.totient 78029614350786272055749865667 = 77505588839973269792038413312 := by
  rw [← show ((([(173, 1), (1063, 1), (11940457, 1), (35535231074319569, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_173, prime_sixtySixBL_1063, prime_sixtySixBL_11940457, prime_sixtySixBL_35535231074319569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865668 : Nat.totient 78029614350786272055749865668 = 34163449664016277127146176000 := by
  rw [← show ((([(2, 2), (11, 1), (29, 1), (421, 1), (189613, 1), (766052581993438991, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_11, prime_sixtySixBL_29, prime_sixtySixBL_421, prime_sixtySixBL_189613, prime_sixtySixBL_766052581993438991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865669 : Nat.totient 78029614350786272055749865669 = 44585943609233125594035505920 := by
  rw [← show ((([(3, 1), (7, 1), (18521, 1), (200620696585822199397209, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_7, prime_sixtySixBL_18521, prime_sixtySixBL_200620696585822199397209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865670 : Nat.totient 78029614350786272055749865670 = 28720040590616315783913455616 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (43, 1), (67, 1), (5483, 1), (2354867329, 1), (9120185587, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_23, prime_sixtySixBL_43, prime_sixtySixBL_67, prime_sixtySixBL_5483, prime_sixtySixBL_2354867329, prime_sixtySixBL_9120185587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865671 : Nat.totient 78029614350786272055749865671 = 75512530016889940699112773200 := by
  rw [← show ((([(31, 1), (2517084333896331356637092441, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_31, prime_sixtySixBL_2517084333896331356637092441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865672 : Nat.totient 78029614350786272055749865672 = 26009871450262090685249955216 := by
  rw [← show ((([(2, 3), (3, 1), (3251233931282761335656244403, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_3251233931282761335656244403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865673 : Nat.totient 78029614350786272055749865673 = 72027336323802712666846029840 := by
  rw [← show ((([(13, 1), (6002278026983559388903835821, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_13, prime_sixtySixBL_6002278026983559388903835821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865674 : Nat.totient 78029614350786272055749865674 = 38886768713827173688196060160 := by
  rw [← show ((([(2, 1), (331, 1), (3853, 1), (551113, 1), (12345017, 1), (4496453579, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_331, prime_sixtySixBL_3853, prime_sixtySixBL_551113, prime_sixtySixBL_12345017, prime_sixtySixBL_4496453579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865675 : Nat.totient 78029614350786272055749865675 = 41559476786707322865364243200 := by
  rw [← show ((([(3, 2), (5, 2), (739, 1), (10727021, 1), (43747513430671837, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_739, prime_sixtySixBL_10727021, prime_sixtySixBL_43747513430671837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865676 : Nat.totient 78029614350786272055749865676 = 33441091821350412094363190400 := by
  rw [← show ((([(2, 2), (7, 1), (195043, 1), (2091491951, 1), (6831480976169, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_7, prime_sixtySixBL_195043, prime_sixtySixBL_2091491951, prime_sixtySixBL_6831480976169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865677 : Nat.totient 78029614350786272055749865677 = 76401470475149290031719440000 := by
  rw [← show ((([(59, 1), (251, 1), (35557273, 1), (148185353739191261, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_59, prime_sixtySixBL_251, prime_sixtySixBL_35557273, prime_sixtySixBL_148185353739191261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865678 : Nat.totient 78029614350786272055749865678 = 25951158422157661586637651960 := by
  rw [← show ((([(2, 1), (3, 1), (443, 1), (29356514052214549306151191, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_443, prime_sixtySixBL_29356514052214549306151191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865679 : Nat.totient 78029614350786272055749865679 = 69018823504380977739729610560 := by
  rw [← show ((([(11, 1), (37, 1), (191718954178836049277026697, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_11, prime_sixtySixBL_37, prime_sixtySixBL_191718954178836049277026697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865680 : Nat.totient 78029614350786272055749865680 = 31182958538200002298648121856 := by
  rw [← show ((([(2, 4), (5, 1), (1087, 1), (179779, 1), (4991153988214019677, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_1087, prime_sixtySixBL_179779, prime_sixtySixBL_4991153988214019677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865681 : Nat.totient 78029614350786272055749865681 = 48905735654352949454685597696 := by
  rw [← show ((([(3, 1), (17, 1), (907, 1), (1151209, 1), (1465304290093910137, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_17, prime_sixtySixBL_907, prime_sixtySixBL_1151209, prime_sixtySixBL_1465304290093910137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865682 : Nat.totient 78029614350786272055749865682 = 36488405719753182046573113600 := by
  rw [← show ((([(2, 1), (19, 1), (79, 1), (7121, 1), (3650125416121793075821, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_19, prime_sixtySixBL_79, prime_sixtySixBL_7121, prime_sixtySixBL_3650125416121793075821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865683 : Nat.totient 78029614350786272055749865683 = 65437768942785654854173547904 := by
  rw [← show ((([(7, 1), (47, 1), (4229, 1), (10477, 1), (5352897575291494619, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_7, prime_sixtySixBL_47, prime_sixtySixBL_4229, prime_sixtySixBL_10477, prime_sixtySixBL_5352897575291494619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865684 : Nat.totient 78029614350786272055749865684 = 26009756667576002529890827200 := by
  rw [← show ((([(2, 2), (3, 3), (226601, 1), (3188407946893204193623, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_226601, prime_sixtySixBL_3188407946893204193623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865685 : Nat.totient 78029614350786272055749865685 = 62155775890944610515673385472 := by
  rw [← show ((([(5, 1), (233, 1), (22596253, 1), (2964129041357617213, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_233, prime_sixtySixBL_22596253, prime_sixtySixBL_2964129041357617213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865686 : Nat.totient 78029614350786272055749865686 = 36013654630116487956571571424 := by
  rw [← show ((([(2, 1), (13, 1), (2661413, 1), (1127648739031401625547, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_13, prime_sixtySixBL_2661413, prime_sixtySixBL_1127648739031401625547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865687 : Nat.totient 78029614350786272055749865687 = 51947392771316220061222440440 := by
  rw [← show ((([(3, 1), (719, 1), (36175064603980654638734291, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_719, prime_sixtySixBL_36175064603980654638734291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865688 : Nat.totient 78029614350786272055749865688 = 37693679660914571599249747200 := by
  rw [← show ((([(2, 3), (41, 1), (103, 1), (39134111, 1), (59019145802180987, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_41, prime_sixtySixBL_103, prime_sixtySixBL_39134111, prime_sixtySixBL_59019145802180987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865689 : Nat.totient 78029614350786272055749865689 = 77843386153811236012460692000 := by
  rw [← show ((([(419, 1), (179484641051, 1), (1037571769098281, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_419, prime_sixtySixBL_179484641051, prime_sixtySixBL_1037571769098281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865690 : Nat.totient 78029614350786272055749865690 = 16212305908682353439738265600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (9887, 1), (3463574321, 1), (986412200737, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_5, prime_sixtySixBL_7, prime_sixtySixBL_11, prime_sixtySixBL_9887, prime_sixtySixBL_3463574321, prime_sixtySixBL_986412200737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865691 : Nat.totient 78029614350786272055749865691 = 77973823727532525861711407520 := by
  rw [← show ((([(1429, 1), (65731, 1), (830724448752158220709, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_1429, prime_sixtySixBL_65731, prime_sixtySixBL_830724448752158220709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865692 : Nat.totient 78029614350786272055749865692 = 38628521955834788146410824400 := by
  rw [← show ((([(2, 2), (101, 1), (193142609779173940732054123, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_101, prime_sixtySixBL_193142609779173940732054123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865693 : Nat.totient 78029614350786272055749865693 = 49758014948327477832652088136 := by
  rw [← show ((([(3, 2), (23, 1), (376954658699450589641303699, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_23, prime_sixtySixBL_376954658699450589641303699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865694 : Nat.totient 78029614350786272055749865694 = 39014807038058598605236466160 := by
  rw [← show ((([(2, 1), (284085911, 1), (137334537422354380777, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_284085911, prime_sixtySixBL_137334537422354380777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865695 : Nat.totient 78029614350786272055749865695 = 62414539875862328078031024000 := by
  rw [← show ((([(5, 1), (7951, 1), (48187, 1), (11839237, 1), (3440440878331, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_5, prime_sixtySixBL_7951, prime_sixtySixBL_48187, prime_sixtySixBL_11839237, prime_sixtySixBL_3440440878331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865696 : Nat.totient 78029614350786272055749865696 = 26009871450262090685249955200 := by
  rw [← show ((([(2, 5), (3, 1), (812808482820690333914061101, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_3, prime_sixtySixBL_812808482820690333914061101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865697 : Nat.totient 78029614350786272055749865697 = 64251721799046818165741629248 := by
  rw [← show ((([(7, 1), (29, 1), (199, 1), (9067567, 1), (213019603954706603, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_7, prime_sixtySixBL_29, prime_sixtySixBL_199, prime_sixtySixBL_9067567, prime_sixtySixBL_213019603954706603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865698 : Nat.totient 78029614350786272055749865698 = 36567442620914057188239052800 := by
  rw [← show ((([(2, 1), (17, 1), (241, 1), (3178421, 1), (2996070851512083277, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_17, prime_sixtySixBL_241, prime_sixtySixBL_3178421, prime_sixtySixBL_2996070851512083277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865699 : Nat.totient 78029614350786272055749865699 = 47476356776114061233210572800 := by
  rw [← show ((([(3, 1), (13, 1), (97, 1), (1021, 1), (164581, 1), (122748920177812853, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_3, prime_sixtySixBL_13, prime_sixtySixBL_97, prime_sixtySixBL_1021, prime_sixtySixBL_164581, prime_sixtySixBL_122748920177812853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865700 : Nat.totient 78029614350786272055749865700 = 31211845740314508822299946240 := by
  rw [← show ((([(2, 2), (5, 2), (780296143507862720557498657, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_2, prime_sixtySixBL_5, prime_sixtySixBL_780296143507862720557498657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtySixBL_78029614350786272055749865701 : Nat.totient 78029614350786272055749865701 = 67202538674820125810840812800 := by
  rw [← show ((([(11, 1), (19, 1), (134898715409, 1), (2767612989887621, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786272055749865701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtySixBL_11, prime_sixtySixBL_19, prime_sixtySixBL_134898715409, prime_sixtySixBL_2767612989887621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtySixBL : certifiedKill 2 78029614350786272055749865599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtySixBL_78029614350786272055749865600, phi_sixtySixBL_78029614350786272055749865601, phi_sixtySixBL_78029614350786272055749865602,
    phi_sixtySixBL_78029614350786272055749865603, phi_sixtySixBL_78029614350786272055749865604, phi_sixtySixBL_78029614350786272055749865605,
    phi_sixtySixBL_78029614350786272055749865606, phi_sixtySixBL_78029614350786272055749865607, phi_sixtySixBL_78029614350786272055749865608,
    phi_sixtySixBL_78029614350786272055749865609, phi_sixtySixBL_78029614350786272055749865610, phi_sixtySixBL_78029614350786272055749865611,
    phi_sixtySixBL_78029614350786272055749865612, phi_sixtySixBL_78029614350786272055749865613, phi_sixtySixBL_78029614350786272055749865614,
    phi_sixtySixBL_78029614350786272055749865615, phi_sixtySixBL_78029614350786272055749865616, phi_sixtySixBL_78029614350786272055749865617,
    phi_sixtySixBL_78029614350786272055749865618, phi_sixtySixBL_78029614350786272055749865619, phi_sixtySixBL_78029614350786272055749865620,
    phi_sixtySixBL_78029614350786272055749865621, phi_sixtySixBL_78029614350786272055749865622, phi_sixtySixBL_78029614350786272055749865623,
    phi_sixtySixBL_78029614350786272055749865624, phi_sixtySixBL_78029614350786272055749865625, phi_sixtySixBL_78029614350786272055749865626,
    phi_sixtySixBL_78029614350786272055749865627, phi_sixtySixBL_78029614350786272055749865628, phi_sixtySixBL_78029614350786272055749865629,
    phi_sixtySixBL_78029614350786272055749865630, phi_sixtySixBL_78029614350786272055749865631, phi_sixtySixBL_78029614350786272055749865632,
    phi_sixtySixBL_78029614350786272055749865633, phi_sixtySixBL_78029614350786272055749865634, phi_sixtySixBL_78029614350786272055749865635,
    phi_sixtySixBL_78029614350786272055749865636, phi_sixtySixBL_78029614350786272055749865637, phi_sixtySixBL_78029614350786272055749865638,
    phi_sixtySixBL_78029614350786272055749865639, phi_sixtySixBL_78029614350786272055749865640, phi_sixtySixBL_78029614350786272055749865641,
    phi_sixtySixBL_78029614350786272055749865642, phi_sixtySixBL_78029614350786272055749865643, phi_sixtySixBL_78029614350786272055749865644,
    phi_sixtySixBL_78029614350786272055749865645, phi_sixtySixBL_78029614350786272055749865646, phi_sixtySixBL_78029614350786272055749865647,
    phi_sixtySixBL_78029614350786272055749865648, phi_sixtySixBL_78029614350786272055749865649, phi_sixtySixBL_78029614350786272055749865650,
    phi_sixtySixBL_78029614350786272055749865651, phi_sixtySixBL_78029614350786272055749865652, phi_sixtySixBL_78029614350786272055749865653,
    phi_sixtySixBL_78029614350786272055749865654, phi_sixtySixBL_78029614350786272055749865655, phi_sixtySixBL_78029614350786272055749865656,
    phi_sixtySixBL_78029614350786272055749865657, phi_sixtySixBL_78029614350786272055749865658, phi_sixtySixBL_78029614350786272055749865659,
    phi_sixtySixBL_78029614350786272055749865660, phi_sixtySixBL_78029614350786272055749865661, phi_sixtySixBL_78029614350786272055749865662,
    phi_sixtySixBL_78029614350786272055749865663, phi_sixtySixBL_78029614350786272055749865664, phi_sixtySixBL_78029614350786272055749865665,
    phi_sixtySixBL_78029614350786272055749865666, phi_sixtySixBL_78029614350786272055749865667, phi_sixtySixBL_78029614350786272055749865668,
    phi_sixtySixBL_78029614350786272055749865669, phi_sixtySixBL_78029614350786272055749865670, phi_sixtySixBL_78029614350786272055749865671,
    phi_sixtySixBL_78029614350786272055749865672, phi_sixtySixBL_78029614350786272055749865673, phi_sixtySixBL_78029614350786272055749865674,
    phi_sixtySixBL_78029614350786272055749865675, phi_sixtySixBL_78029614350786272055749865676, phi_sixtySixBL_78029614350786272055749865677,
    phi_sixtySixBL_78029614350786272055749865678, phi_sixtySixBL_78029614350786272055749865679, phi_sixtySixBL_78029614350786272055749865680,
    phi_sixtySixBL_78029614350786272055749865681, phi_sixtySixBL_78029614350786272055749865682, phi_sixtySixBL_78029614350786272055749865683,
    phi_sixtySixBL_78029614350786272055749865684, phi_sixtySixBL_78029614350786272055749865685, phi_sixtySixBL_78029614350786272055749865686,
    phi_sixtySixBL_78029614350786272055749865687, phi_sixtySixBL_78029614350786272055749865688, phi_sixtySixBL_78029614350786272055749865689,
    phi_sixtySixBL_78029614350786272055749865690, phi_sixtySixBL_78029614350786272055749865691, phi_sixtySixBL_78029614350786272055749865692,
    phi_sixtySixBL_78029614350786272055749865693, phi_sixtySixBL_78029614350786272055749865694, phi_sixtySixBL_78029614350786272055749865695,
    phi_sixtySixBL_78029614350786272055749865696, phi_sixtySixBL_78029614350786272055749865697, phi_sixtySixBL_78029614350786272055749865698,
    phi_sixtySixBL_78029614350786272055749865699, phi_sixtySixBL_78029614350786272055749865700, phi_sixtySixBL_78029614350786272055749865701]

end TotientTailPeriodKiller
end Erdos249257
