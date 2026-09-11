import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortySevenASFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortySevenASFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortySevenASFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortySevenASFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortySevenASFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortySevenASFastPow a n * fortySevenASFastPow a n * a
        else fortySevenASFastPow a n * fortySevenASFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortySevenAS_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortySevenAS_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortySevenAS_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortySevenAS_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortySevenAS_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortySevenAS_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortySevenAS_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortySevenAS_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortySevenAS_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortySevenAS_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortySevenAS_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortySevenAS_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortySevenAS_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortySevenAS_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortySevenAS_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortySevenAS_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortySevenAS_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortySevenAS_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortySevenAS_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortySevenAS_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortySevenAS_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortySevenAS_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortySevenAS_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortySevenAS_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortySevenAS_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortySevenAS_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortySevenAS_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortySevenAS_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortySevenAS_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortySevenAS_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortySevenAS_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortySevenAS_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortySevenAS_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortySevenAS_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortySevenAS_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortySevenAS_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortySevenAS_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortySevenAS_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortySevenAS_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortySevenAS_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortySevenAS_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortySevenAS_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortySevenAS_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortySevenAS_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortySevenAS_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortySevenAS_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortySevenAS_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortySevenAS_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortySevenAS_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortySevenAS_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortySevenAS_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortySevenAS_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortySevenAS_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortySevenAS_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortySevenAS_271 : Nat.Prime 271 := by norm_num
private theorem prime_fortySevenAS_277 : Nat.Prime 277 := by norm_num
private theorem prime_fortySevenAS_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortySevenAS_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortySevenAS_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortySevenAS_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortySevenAS_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortySevenAS_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortySevenAS_367 : Nat.Prime 367 := by norm_num
private theorem prime_fortySevenAS_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortySevenAS_389 : Nat.Prime 389 := by norm_num
private theorem prime_fortySevenAS_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortySevenAS_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortySevenAS_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortySevenAS_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortySevenAS_431 : Nat.Prime 431 := by norm_num
private theorem prime_fortySevenAS_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortySevenAS_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortySevenAS_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortySevenAS_463 : Nat.Prime 463 := by norm_num
private theorem prime_fortySevenAS_467 : Nat.Prime 467 := by norm_num
private theorem prime_fortySevenAS_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortySevenAS_487 : Nat.Prime 487 := by norm_num
private theorem prime_fortySevenAS_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortySevenAS_547 : Nat.Prime 547 := by norm_num
private theorem prime_fortySevenAS_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortySevenAS_569 : Nat.Prime 569 := by norm_num
private theorem prime_fortySevenAS_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortySevenAS_601 : Nat.Prime 601 := by norm_num
private theorem prime_fortySevenAS_607 : Nat.Prime 607 := by norm_num
private theorem prime_fortySevenAS_619 : Nat.Prime 619 := by norm_num
private theorem prime_fortySevenAS_643 : Nat.Prime 643 := by norm_num
private theorem prime_fortySevenAS_673 : Nat.Prime 673 := by norm_num
private theorem prime_fortySevenAS_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortySevenAS_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortySevenAS_719 : Nat.Prime 719 := by norm_num
private theorem prime_fortySevenAS_757 : Nat.Prime 757 := by norm_num
private theorem prime_fortySevenAS_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortySevenAS_773 : Nat.Prime 773 := by norm_num
private theorem prime_fortySevenAS_809 : Nat.Prime 809 := by norm_num
private theorem prime_fortySevenAS_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortySevenAS_839 : Nat.Prime 839 := by norm_num
private theorem prime_fortySevenAS_883 : Nat.Prime 883 := by norm_num
private theorem prime_fortySevenAS_929 : Nat.Prime 929 := by norm_num
private theorem prime_fortySevenAS_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortySevenAS_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_fortySevenAS_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fortySevenAS_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fortySevenAS_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fortySevenAS_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_fortySevenAS_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortySevenAS_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortySevenAS_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fortySevenAS_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_fortySevenAS_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fortySevenAS_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_fortySevenAS_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fortySevenAS_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_fortySevenAS_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_fortySevenAS_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortySevenAS_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_fortySevenAS_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_fortySevenAS_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_fortySevenAS_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_fortySevenAS_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fortySevenAS_1699 : Nat.Prime 1699 := by norm_num
private theorem prime_fortySevenAS_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_fortySevenAS_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_fortySevenAS_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_fortySevenAS_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_fortySevenAS_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_fortySevenAS_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_fortySevenAS_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_fortySevenAS_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fortySevenAS_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_fortySevenAS_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_fortySevenAS_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_fortySevenAS_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fortySevenAS_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_fortySevenAS_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortySevenAS_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_fortySevenAS_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_fortySevenAS_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_fortySevenAS_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_fortySevenAS_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_fortySevenAS_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_fortySevenAS_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_fortySevenAS_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_fortySevenAS_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_fortySevenAS_3491 : Nat.Prime 3491 := by norm_num
private theorem prime_fortySevenAS_3529 : Nat.Prime 3529 := by norm_num
private theorem prime_fortySevenAS_3571 : Nat.Prime 3571 := by norm_num
private theorem prime_fortySevenAS_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_fortySevenAS_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_fortySevenAS_3929 : Nat.Prime 3929 := by norm_num
private theorem prime_fortySevenAS_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_fortySevenAS_4513 : Nat.Prime 4513 := by norm_num
private theorem prime_fortySevenAS_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_fortySevenAS_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_fortySevenAS_4721 : Nat.Prime 4721 := by norm_num
private theorem prime_fortySevenAS_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_fortySevenAS_4751 : Nat.Prime 4751 := by norm_num
private theorem prime_fortySevenAS_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortySevenAS_5099 : Nat.Prime 5099 := by norm_num
private theorem prime_fortySevenAS_5297 : Nat.Prime 5297 := by norm_num
private theorem prime_fortySevenAS_5557 : Nat.Prime 5557 := by norm_num
private theorem prime_fortySevenAS_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_fortySevenAS_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_fortySevenAS_6553 : Nat.Prime 6553 := by norm_num
private theorem prime_fortySevenAS_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortySevenAS_6781 : Nat.Prime 6781 := by norm_num
private theorem prime_fortySevenAS_6947 : Nat.Prime 6947 := by norm_num
private theorem prime_fortySevenAS_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_fortySevenAS_7607 : Nat.Prime 7607 := by norm_num
private theorem prime_fortySevenAS_7639 : Nat.Prime 7639 := by norm_num
private theorem prime_fortySevenAS_7669 : Nat.Prime 7669 := by norm_num
private theorem prime_fortySevenAS_8011 : Nat.Prime 8011 := by norm_num
private theorem prime_fortySevenAS_8297 : Nat.Prime 8297 := by norm_num
private theorem prime_fortySevenAS_8353 : Nat.Prime 8353 := by norm_num
private theorem prime_fortySevenAS_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_fortySevenAS_8419 : Nat.Prime 8419 := by norm_num
private theorem prime_fortySevenAS_8447 : Nat.Prime 8447 := by norm_num
private theorem prime_fortySevenAS_9323 : Nat.Prime 9323 := by norm_num
private theorem prime_fortySevenAS_9829 : Nat.Prime 9829 := by norm_num
private theorem prime_fortySevenAS_10007 : Nat.Prime 10007 := by norm_num
private theorem prime_fortySevenAS_10009 : Nat.Prime 10009 := by norm_num
private theorem prime_fortySevenAS_10399 : Nat.Prime 10399 := by norm_num
private theorem prime_fortySevenAS_11047 : Nat.Prime 11047 := by norm_num
private theorem prime_fortySevenAS_11801 : Nat.Prime 11801 := by norm_num
private theorem prime_fortySevenAS_12161 : Nat.Prime 12161 := by norm_num
private theorem prime_fortySevenAS_12457 : Nat.Prime 12457 := by norm_num
private theorem prime_fortySevenAS_12473 : Nat.Prime 12473 := by norm_num
private theorem prime_fortySevenAS_12527 : Nat.Prime 12527 := by norm_num
private theorem prime_fortySevenAS_12569 : Nat.Prime 12569 := by norm_num
private theorem prime_fortySevenAS_14149 : Nat.Prime 14149 := by norm_num
private theorem prime_fortySevenAS_14843 : Nat.Prime 14843 := by norm_num
private theorem prime_fortySevenAS_15299 : Nat.Prime 15299 := by norm_num
private theorem prime_fortySevenAS_15901 : Nat.Prime 15901 := by norm_num
private theorem prime_fortySevenAS_16067 : Nat.Prime 16067 := by norm_num
private theorem prime_fortySevenAS_16369 : Nat.Prime 16369 := by norm_num
private theorem prime_fortySevenAS_17317 : Nat.Prime 17317 := by norm_num
private theorem prime_fortySevenAS_18077 : Nat.Prime 18077 := by norm_num
private theorem prime_fortySevenAS_18127 : Nat.Prime 18127 := by norm_num
private theorem prime_fortySevenAS_18341 : Nat.Prime 18341 := by norm_num
private theorem prime_fortySevenAS_18671 : Nat.Prime 18671 := by norm_num
private theorem prime_fortySevenAS_18959 : Nat.Prime 18959 := by norm_num
private theorem prime_fortySevenAS_21023 : Nat.Prime 21023 := by norm_num
private theorem prime_fortySevenAS_21503 : Nat.Prime 21503 := by norm_num
private theorem prime_fortySevenAS_22283 : Nat.Prime 22283 := by norm_num
private theorem prime_fortySevenAS_22349 : Nat.Prime 22349 := by norm_num
private theorem prime_fortySevenAS_23321 : Nat.Prime 23321 := by norm_num
private theorem prime_fortySevenAS_23567 : Nat.Prime 23567 := by norm_num
private theorem prime_fortySevenAS_23599 : Nat.Prime 23599 := by norm_num
private theorem prime_fortySevenAS_24413 : Nat.Prime 24413 := by norm_num
private theorem prime_fortySevenAS_24551 : Nat.Prime 24551 := by norm_num
private theorem prime_fortySevenAS_29723 : Nat.Prime 29723 := by norm_num
private theorem prime_fortySevenAS_29819 : Nat.Prime 29819 := by norm_num
private theorem prime_fortySevenAS_30983 : Nat.Prime 30983 := by norm_num
private theorem prime_fortySevenAS_31271 : Nat.Prime 31271 := by norm_num
private theorem prime_fortySevenAS_32969 : Nat.Prime 32969 := by norm_num
private theorem prime_fortySevenAS_33311 : Nat.Prime 33311 := by norm_num
private theorem prime_fortySevenAS_33479 : Nat.Prime 33479 := by norm_num
private theorem prime_fortySevenAS_34369 : Nat.Prime 34369 := by norm_num
private theorem prime_fortySevenAS_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortySevenAS_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_fortySevenAS_37243 : Nat.Prime 37243 := by norm_num
private theorem prime_fortySevenAS_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortySevenAS_40099 : Nat.Prime 40099 := by norm_num
private theorem prime_fortySevenAS_41491 : Nat.Prime 41491 := by norm_num
private theorem prime_fortySevenAS_41579 : Nat.Prime 41579 := by norm_num
private theorem prime_fortySevenAS_42499 : Nat.Prime 42499 := by norm_num
private theorem prime_fortySevenAS_43159 : Nat.Prime 43159 := by norm_num
private theorem prime_fortySevenAS_43189 : Nat.Prime 43189 := by norm_num
private theorem prime_fortySevenAS_43987 : Nat.Prime 43987 := by norm_num
private theorem prime_fortySevenAS_44497 : Nat.Prime 44497 := by norm_num
private theorem prime_fortySevenAS_45503 : Nat.Prime 45503 := by norm_num
private theorem prime_fortySevenAS_46681 : Nat.Prime 46681 := by norm_num
private theorem prime_fortySevenAS_49789 : Nat.Prime 49789 := by norm_num
private theorem prime_fortySevenAS_54367 : Nat.Prime 54367 := by norm_num
private theorem prime_fortySevenAS_54497 : Nat.Prime 54497 := by norm_num
private theorem prime_fortySevenAS_55997 : Nat.Prime 55997 := by norm_num
private theorem prime_fortySevenAS_58207 : Nat.Prime 58207 := by norm_num
private theorem prime_fortySevenAS_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortySevenAS_62687 : Nat.Prime 62687 := by norm_num
private theorem prime_fortySevenAS_67429 : Nat.Prime 67429 := by norm_num
private theorem prime_fortySevenAS_68279 : Nat.Prime 68279 := by norm_num
private theorem prime_fortySevenAS_71741 : Nat.Prime 71741 := by norm_num
private theorem prime_fortySevenAS_79337 : Nat.Prime 79337 := by norm_num
private theorem prime_fortySevenAS_80537 : Nat.Prime 80537 := by norm_num
private theorem prime_fortySevenAS_80629 : Nat.Prime 80629 := by norm_num
private theorem prime_fortySevenAS_81283 : Nat.Prime 81283 := by norm_num
private theorem prime_fortySevenAS_83987 : Nat.Prime 83987 := by norm_num
private theorem prime_fortySevenAS_96259 : Nat.Prime 96259 := by norm_num
private theorem prime_fortySevenAS_98711 : Nat.Prime 98711 := by norm_num
private theorem prime_fortySevenAS_100537 : Nat.Prime 100537 := by norm_num
private theorem prime_fortySevenAS_101363 : Nat.Prime 101363 := by norm_num
private theorem prime_fortySevenAS_102653 : Nat.Prime 102653 := by norm_num
private theorem prime_fortySevenAS_102769 : Nat.Prime 102769 := by norm_num
private theorem prime_fortySevenAS_104393 : Nat.Prime 104393 := by norm_num
private theorem prime_fortySevenAS_105361 : Nat.Prime 105361 := by norm_num
private theorem prime_fortySevenAS_107273 : Nat.Prime 107273 := by norm_num
private theorem prime_fortySevenAS_108301 : Nat.Prime 108301 := by norm_num
private theorem prime_fortySevenAS_116849 : Nat.Prime 116849 := by norm_num
private theorem prime_fortySevenAS_117541 : Nat.Prime 117541 := by norm_num
private theorem prime_fortySevenAS_117617 : Nat.Prime 117617 := by norm_num
private theorem prime_fortySevenAS_123083 : Nat.Prime 123083 := by norm_num
private theorem prime_fortySevenAS_128099 : Nat.Prime 128099 := by norm_num
private theorem prime_fortySevenAS_131687 : Nat.Prime 131687 := by norm_num
private theorem prime_fortySevenAS_133919 : Nat.Prime 133919 := by norm_num
private theorem prime_fortySevenAS_138793 : Nat.Prime 138793 := by norm_num
private theorem prime_fortySevenAS_158537 : Nat.Prime 158537 := by norm_num
private theorem prime_fortySevenAS_176329 : Nat.Prime 176329 := by norm_num
private theorem prime_fortySevenAS_177761 : Nat.Prime 177761 := by norm_num
private theorem prime_fortySevenAS_177889 : Nat.Prime 177889 := by norm_num
private theorem prime_fortySevenAS_184901 : Nat.Prime 184901 := by norm_num
private theorem prime_fortySevenAS_211151 : Nat.Prime 211151 := by norm_num
private theorem prime_fortySevenAS_215051 : Nat.Prime 215051 := by norm_num
private theorem prime_fortySevenAS_216649 : Nat.Prime 216649 := by norm_num
private theorem prime_fortySevenAS_222149 : Nat.Prime 222149 := by norm_num
private theorem prime_fortySevenAS_251149 : Nat.Prime 251149 := by norm_num
private theorem prime_fortySevenAS_270913 : Nat.Prime 270913 := by norm_num
private theorem prime_fortySevenAS_294751 : Nat.Prime 294751 := by norm_num
private theorem prime_fortySevenAS_301349 : Nat.Prime 301349 := by norm_num
private theorem prime_fortySevenAS_301813 : Nat.Prime 301813 := by norm_num
private theorem prime_fortySevenAS_309083 : Nat.Prime 309083 := by norm_num
private theorem prime_fortySevenAS_311653 : Nat.Prime 311653 := by norm_num
private theorem prime_fortySevenAS_313307 : Nat.Prime 313307 := by norm_num
private theorem prime_fortySevenAS_315349 : Nat.Prime 315349 := by norm_num
private theorem prime_fortySevenAS_328381 : Nat.Prime 328381 := by norm_num
private theorem prime_fortySevenAS_330703 : Nat.Prime 330703 := by norm_num
private theorem prime_fortySevenAS_335089 : Nat.Prime 335089 := by norm_num
private theorem prime_fortySevenAS_365231 : Nat.Prime 365231 := by norm_num
private theorem prime_fortySevenAS_379123 : Nat.Prime 379123 := by norm_num
private theorem prime_fortySevenAS_380441 : Nat.Prime 380441 := by norm_num
private theorem prime_fortySevenAS_381757 : Nat.Prime 381757 := by norm_num
private theorem prime_fortySevenAS_399097 : Nat.Prime 399097 := by norm_num
private theorem prime_fortySevenAS_401519 : Nat.Prime 401519 := by norm_num
private theorem prime_fortySevenAS_415523 : Nat.Prime 415523 := by norm_num
private theorem prime_fortySevenAS_467531 : Nat.Prime 467531 := by norm_num
private theorem prime_fortySevenAS_481489 : Nat.Prime 481489 := by norm_num
private theorem prime_fortySevenAS_495527 : Nat.Prime 495527 := by norm_num
private theorem prime_fortySevenAS_528623 : Nat.Prime 528623 := by norm_num
private theorem prime_fortySevenAS_600931 : Nat.Prime 600931 := by norm_num
private theorem prime_fortySevenAS_624643 : Nat.Prime 624643 := by norm_num
private theorem prime_fortySevenAS_632503 : Nat.Prime 632503 := by norm_num
private theorem prime_fortySevenAS_654601 : Nat.Prime 654601 := by norm_num
private theorem prime_fortySevenAS_663001 : Nat.Prime 663001 := by norm_num
private theorem prime_fortySevenAS_669311 : Nat.Prime 669311 := by norm_num
private theorem prime_fortySevenAS_670051 : Nat.Prime 670051 := by norm_num
private theorem prime_fortySevenAS_720127 : Nat.Prime 720127 := by norm_num
private theorem prime_fortySevenAS_825613 : Nat.Prime 825613 := by norm_num
private theorem prime_fortySevenAS_825991 : Nat.Prime 825991 := by norm_num
private theorem prime_fortySevenAS_835511 : Nat.Prime 835511 := by norm_num
private theorem prime_fortySevenAS_863879 : Nat.Prime 863879 := by norm_num
private theorem prime_fortySevenAS_880247 : Nat.Prime 880247 := by norm_num
private theorem prime_fortySevenAS_899881 : Nat.Prime 899881 := by norm_num
private theorem prime_fortySevenAS_946123 : Nat.Prime 946123 := by norm_num
private theorem prime_fortySevenAS_1077469 : Nat.Prime 1077469 := by norm_num
private theorem prime_fortySevenAS_1085509 : Nat.Prime 1085509 := by norm_num
private theorem prime_fortySevenAS_1090181 : Nat.Prime 1090181 := by norm_num
private theorem prime_fortySevenAS_1093427 : Nat.Prime 1093427 := by norm_num
private theorem prime_fortySevenAS_1190417 : Nat.Prime 1190417 := by norm_num
private theorem prime_fortySevenAS_1300597 : Nat.Prime 1300597 := by norm_num
private theorem prime_fortySevenAS_1318663 : Nat.Prime 1318663 := by norm_num
private theorem prime_fortySevenAS_1361599 : Nat.Prime 1361599 := by norm_num
private theorem prime_fortySevenAS_1385767 : Nat.Prime 1385767 := by norm_num
private theorem prime_fortySevenAS_1402493 : Nat.Prime 1402493 := by norm_num
private theorem prime_fortySevenAS_1447247 : Nat.Prime 1447247 := by norm_num
private theorem prime_fortySevenAS_1465643 : Nat.Prime 1465643 := by norm_num
private theorem prime_fortySevenAS_1487383 : Nat.Prime 1487383 := by norm_num
private theorem prime_fortySevenAS_1495853 : Nat.Prime 1495853 := by norm_num
private theorem prime_fortySevenAS_1760923 : Nat.Prime 1760923 := by norm_num
private theorem prime_fortySevenAS_1865161 : Nat.Prime 1865161 := by norm_num
private theorem prime_fortySevenAS_1992533 : Nat.Prime 1992533 := by norm_num
private theorem prime_fortySevenAS_2207929 : Nat.Prime 2207929 := by norm_num
private theorem prime_fortySevenAS_2219023 : Nat.Prime 2219023 := by norm_num
private theorem prime_fortySevenAS_2326283 : Nat.Prime 2326283 := by norm_num
private theorem prime_fortySevenAS_2486041 : Nat.Prime 2486041 := by norm_num
private theorem prime_fortySevenAS_2599679 : Nat.Prime 2599679 := by norm_num
private theorem prime_fortySevenAS_2624693 : Nat.Prime 2624693 := by norm_num
private theorem prime_fortySevenAS_2784581 : Nat.Prime 2784581 := by norm_num
private theorem prime_fortySevenAS_2947621 : Nat.Prime 2947621 := by norm_num
private theorem prime_fortySevenAS_3328159 : Nat.Prime 3328159 := by norm_num
private theorem prime_fortySevenAS_3428267 : Nat.Prime 3428267 := by norm_num
private theorem prime_fortySevenAS_3430331 : Nat.Prime 3430331 := by norm_num
private theorem prime_fortySevenAS_3522413 : Nat.Prime 3522413 := by norm_num
private theorem prime_fortySevenAS_3834631 : Nat.Prime 3834631 := by norm_num
private theorem prime_fortySevenAS_3954361 : Nat.Prime 3954361 := by norm_num
private theorem prime_fortySevenAS_3956681 : Nat.Prime 3956681 := by norm_num
private theorem prime_fortySevenAS_4180093 : Nat.Prime 4180093 := by norm_num
private theorem prime_fortySevenAS_4477849 : Nat.Prime 4477849 := by norm_num
private theorem prime_fortySevenAS_4500787 : Nat.Prime 4500787 := by norm_num
private theorem prime_fortySevenAS_4543753 : Nat.Prime 4543753 := by norm_num
private theorem prime_fortySevenAS_4603589 : Nat.Prime 4603589 := by norm_num
private theorem prime_fortySevenAS_4692173 : Nat.Prime 4692173 := by norm_num
private theorem prime_fortySevenAS_5301953 : Nat.Prime 5301953 := by norm_num
private theorem prime_fortySevenAS_5742673 : Nat.Prime 5742673 := by norm_num
private theorem prime_fortySevenAS_5872661 : Nat.Prime 5872661 := by norm_num
private theorem prime_fortySevenAS_6017111 : Nat.Prime 6017111 := by norm_num
private theorem prime_fortySevenAS_6496811 : Nat.Prime 6496811 := by norm_num
private theorem prime_fortySevenAS_6630121 : Nat.Prime 6630121 := by norm_num
private theorem prime_fortySevenAS_6879113 : Nat.Prime 6879113 := by norm_num
private theorem prime_fortySevenAS_6990227 : Nat.Prime 6990227 := by norm_num
private theorem prime_fortySevenAS_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortySevenAS_7437511 : Nat.Prime 7437511 := by norm_num
private theorem prime_fortySevenAS_7568963 : Nat.Prime 7568963 := by norm_num
private theorem prime_fortySevenAS_7931179 : Nat.Prime 7931179 := by norm_num
private theorem prime_fortySevenAS_8571809 : Nat.Prime 8571809 := by norm_num
private theorem prime_fortySevenAS_9073319 : Nat.Prime 9073319 := by norm_num
private theorem prime_fortySevenAS_9716621 : Nat.Prime 9716621 := by norm_num
private theorem prime_fortySevenAS_10022183 : Nat.Prime 10022183 := by norm_num
private theorem prime_fortySevenAS_10520701 : Nat.Prime 10520701 := by norm_num
private theorem prime_fortySevenAS_10609153 : Nat.Prime 10609153 := by norm_num
private theorem prime_fortySevenAS_11386939 : Nat.Prime 11386939 := by norm_num
private theorem prime_fortySevenAS_12109919 : Nat.Prime 12109919 := by norm_num
private theorem prime_fortySevenAS_12375911 : Nat.Prime 12375911 := by norm_num
private theorem prime_fortySevenAS_12412753 : Nat.Prime 12412753 := by norm_num
private theorem prime_fortySevenAS_13936387 : Nat.Prime 13936387 := by norm_num
private theorem prime_fortySevenAS_13938361 : Nat.Prime 13938361 := by norm_num
private theorem prime_fortySevenAS_14614693 : Nat.Prime 14614693 := by norm_num
private theorem prime_fortySevenAS_14636107 : Nat.Prime 14636107 := by norm_num
private theorem prime_fortySevenAS_14827583 : Nat.Prime 14827583 := by norm_num
private theorem prime_fortySevenAS_15073789 : Nat.Prime 15073789 := by norm_num
private theorem prime_fortySevenAS_17444461 : Nat.Prime 17444461 := by norm_num
private theorem prime_fortySevenAS_18198379 : Nat.Prime 18198379 := by norm_num
private theorem prime_fortySevenAS_18199127 : Nat.Prime 18199127 := by norm_num
private theorem prime_fortySevenAS_20047373 : Nat.Prime 20047373 := by norm_num
private theorem prime_fortySevenAS_22373189 : Nat.Prime 22373189 := by norm_num
private theorem prime_fortySevenAS_24083671 : Nat.Prime 24083671 := by norm_num
private theorem prime_fortySevenAS_25592351 : Nat.Prime 25592351 := by norm_num
private theorem prime_fortySevenAS_26215169 : Nat.Prime 26215169 := by norm_num
private theorem prime_fortySevenAS_28260697 : Nat.Prime 28260697 := by norm_num
private theorem prime_fortySevenAS_29422439 : Nat.Prime 29422439 := by norm_num
private theorem prime_fortySevenAS_29735449 : Nat.Prime 29735449 := by norm_num

private theorem prime_fortySevenAS_31142477 : Nat.Prime 31142477 := by
  apply lucas_primality 31142477 (2 : ZMod 31142477)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (251149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (251149, 1)] : List FactorBlock).map factorBlockValue).prod) = 31142477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_251149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31142477) ^ 15571238 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31142477) ^ 1004596 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31142477) ^ 124 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_31499267 : Nat.Prime 31499267 := by
  apply lucas_primality 31499267 (2 : ZMod 31499267)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (54497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (54497, 1)] : List FactorBlock).map factorBlockValue).prod) = 31499267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_54497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31499267) ^ 15749633 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31499267) ^ 1852898 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31499267) ^ 578 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_31717381 : Nat.Prime 31717381 := by
  apply lucas_primality 31717381 (2 : ZMod 31717381)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (528623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (528623, 1)] : List FactorBlock).map factorBlockValue).prod) = 31717381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_528623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31717381) ^ 15858690 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31717381) ^ 10572460 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31717381) ^ 6343476 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 31717381) ^ 60 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_34000643 : Nat.Prime 34000643 := by
  apply lucas_primality 34000643 (2 : ZMod 34000643)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (277, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (277, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) = 34000643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_277
      · exact prime_fortySevenAS_4721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34000643) ^ 17000321 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 34000643) ^ 2615434 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 34000643) ^ 122746 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 34000643) ^ 7202 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_35191421 : Nat.Prime 35191421 := by
  apply lucas_primality 35191421 (2 : ZMod 35191421)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (19, 1), (8419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (19, 1), (8419, 1)] : List FactorBlock).map factorBlockValue).prod) = 35191421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_8419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35191421) ^ 17595710 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 35191421) ^ 7038284 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 35191421) ^ 3199220 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 35191421) ^ 1852180 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 35191421) ^ 4180 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_37837981 : Nat.Prime 37837981 := by
  apply lucas_primality 37837981 (6 : ZMod 37837981)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (6781, 1)] : List FactorBlock).map factorBlockValue).prod) = 37837981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_6781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37837981) ^ 18918990 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 37837981) ^ 12612660 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 37837981) ^ 7567596 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 37837981) ^ 1220580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 37837981) ^ 5580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_43389757 : Nat.Prime 43389757 := by
  apply lucas_primality 43389757 (2 : ZMod 43389757)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (133919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (133919, 1)] : List FactorBlock).map factorBlockValue).prod) = 43389757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_133919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43389757) ^ 21694878 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 43389757) ^ 14463252 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 43389757) ^ 324 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_45280717 : Nat.Prime 45280717 := by
  apply lucas_primality 45280717 (2 : ZMod 45280717)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) = 45280717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_10009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45280717) ^ 22640358 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 45280717) ^ 15093572 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 45280717) ^ 3483132 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 45280717) ^ 1561404 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 45280717) ^ 4524 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_46649467 : Nat.Prime 46649467 := by
  apply lucas_primality 46649467 (2 : ZMod 46649467)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (863879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (863879, 1)] : List FactorBlock).map factorBlockValue).prod) = 46649467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_863879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46649467) ^ 23324733 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 46649467) ^ 15549822 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 46649467) ^ 54 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_49651013 : Nat.Prime 49651013 := by
  apply lucas_primality 49651013 (2 : ZMod 49651013)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12412753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12412753, 1)] : List FactorBlock).map factorBlockValue).prod) = 49651013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_12412753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 49651013) ^ 24825506 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 49651013) ^ 4 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_52053259 : Nat.Prime 52053259 := by
  apply lucas_primality 52053259 (10 : ZMod 52053259)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (193, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (193, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 52053259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_79
      · exact prime_fortySevenAS_193
      · exact prime_fortySevenAS_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 52053259) ^ 26026629 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 52053259) ^ 17351086 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 52053259) ^ 658902 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 52053259) ^ 269706 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 52053259) ^ 91482 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_53170927 : Nat.Prime 53170927 := by
  apply lucas_primality 53170927 (3 : ZMod 53170927)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (54367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (54367, 1)] : List FactorBlock).map factorBlockValue).prod) = 53170927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_163
      · exact prime_fortySevenAS_54367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53170927) ^ 26585463 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 53170927) ^ 17723642 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 53170927) ^ 326202 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 53170927) ^ 978 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_54069161 : Nat.Prime 54069161 := by
  apply lucas_primality 54069161 (3 : ZMod 54069161)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (41, 1), (32969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (41, 1), (32969, 1)] : List FactorBlock).map factorBlockValue).prod) = 54069161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_32969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54069161) ^ 27034580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54069161) ^ 10813832 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54069161) ^ 1318760 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54069161) ^ 1640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_57993367 : Nat.Prime 57993367 := by
  apply lucas_primality 57993367 (3 : ZMod 57993367)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (769, 1), (12569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (769, 1), (12569, 1)] : List FactorBlock).map factorBlockValue).prod) = 57993367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_769
      · exact prime_fortySevenAS_12569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57993367) ^ 28996683 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 57993367) ^ 19331122 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 57993367) ^ 75414 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 57993367) ^ 4614 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_63794719 : Nat.Prime 63794719 := by
  apply lucas_primality 63794719 (7 : ZMod 63794719)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (227, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (227, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) = 63794719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_227
      · exact prime_fortySevenAS_1201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 63794719) ^ 31897359 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 63794719) ^ 21264906 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 63794719) ^ 4907286 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 63794719) ^ 281034 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 63794719) ^ 53118 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_66108533 : Nat.Prime 66108533 := by
  apply lucas_primality 66108533 (3 : ZMod 66108533)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (102653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (102653, 1)] : List FactorBlock).map factorBlockValue).prod) = 66108533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_102653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66108533) ^ 33054266 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 66108533) ^ 9444076 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 66108533) ^ 2874284 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 66108533) ^ 644 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_68001287 : Nat.Prime 68001287 := by
  apply lucas_primality 68001287 (5 : ZMod 68001287)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34000643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34000643, 1)] : List FactorBlock).map factorBlockValue).prod) = 68001287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_34000643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 68001287) ^ 34000643 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 68001287) ^ 2 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_74245999 : Nat.Prime 74245999 := by
  apply lucas_primality 74245999 (3 : ZMod 74245999)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (301813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (301813, 1)] : List FactorBlock).map factorBlockValue).prod) = 74245999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_301813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 74245999) ^ 37122999 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 74245999) ^ 24748666 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 74245999) ^ 1810878 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 74245999) ^ 246 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_75272999 : Nat.Prime 75272999 := by
  apply lucas_primality 75272999 (7 : ZMod 75272999)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1597, 1), (23567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1597, 1), (23567, 1)] : List FactorBlock).map factorBlockValue).prod) = 75272999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_1597
      · exact prime_fortySevenAS_23567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 75272999) ^ 37636499 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 75272999) ^ 47134 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 75272999) ^ 3194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_89132759 : Nat.Prime 89132759 := by
  apply lucas_primality 89132759 (7 : ZMod 89132759)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (311653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (311653, 1)] : List FactorBlock).map factorBlockValue).prod) = 89132759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_311653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 89132759) ^ 44566379 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 89132759) ^ 8102978 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 89132759) ^ 6856366 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 89132759) ^ 286 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_91361159 : Nat.Prime 91361159 := by
  apply lucas_primality 91361159 (7 : ZMod 91361159)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 2), (18077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 2), (18077, 1)] : List FactorBlock).map factorBlockValue).prod) = 91361159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_18077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91361159) ^ 45680579 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 91361159) ^ 13051594 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 91361159) ^ 4808482 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 91361159) ^ 5054 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_98787803 : Nat.Prime 98787803 := by
  apply lucas_primality 98787803 (2 : ZMod 98787803)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2599679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2599679, 1)] : List FactorBlock).map factorBlockValue).prod) = 98787803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_2599679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98787803) ^ 49393901 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 98787803) ^ 5199358 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 98787803) ^ 38 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_109194763 : Nat.Prime 109194763 := by
  apply lucas_primality 109194763 (5 : ZMod 109194763)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18199127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18199127, 1)] : List FactorBlock).map factorBlockValue).prod) = 109194763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_18199127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 109194763) ^ 54597381 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 109194763) ^ 36398254 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 109194763) ^ 6 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_114044191 : Nat.Prime 114044191 := by
  apply lucas_primality 114044191 (6 : ZMod 114044191)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (191, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (191, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 114044191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_191
      · exact prime_fortySevenAS_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 114044191) ^ 57022095 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 114044191) ^ 38014730 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 114044191) ^ 22808838 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 114044191) ^ 8772630 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 114044191) ^ 597090 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 114044191) ^ 74490 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_150232751 : Nat.Prime 150232751 := by
  apply lucas_primality 150232751 (7 : ZMod 150232751)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (600931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (600931, 1)] : List FactorBlock).map factorBlockValue).prod) = 150232751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_600931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 150232751) ^ 75116375 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 150232751) ^ 30046550 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 150232751) ^ 250 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_174936383 : Nat.Prime 174936383 := by
  apply lucas_primality 174936383 (5 : ZMod 174936383)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (4603589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (4603589, 1)] : List FactorBlock).map factorBlockValue).prod) = 174936383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_4603589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 174936383) ^ 87468191 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 174936383) ^ 9207178 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 174936383) ^ 38 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_181174579 : Nat.Prime 181174579 := by
  apply lucas_primality 181174579 (2 : ZMod 181174579)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (191, 1), (12161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (191, 1), (12161, 1)] : List FactorBlock).map factorBlockValue).prod) = 181174579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_191
      · exact prime_fortySevenAS_12161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181174579) ^ 90587289 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 181174579) ^ 60391526 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 181174579) ^ 13936506 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 181174579) ^ 948558 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 181174579) ^ 14898 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_188555431 : Nat.Prime 188555431 := by
  apply lucas_primality 188555431 (12 : ZMod 188555431)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (43, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (43, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 188555431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 188555431) ^ 94277715 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 62851810 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 37711086 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 26936490 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 9923970 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 4385010 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (12 : ZMod 188555431) ^ 1200990 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_208213037 : Nat.Prime 208213037 := by
  apply lucas_primality 208213037 (2 : ZMod 208213037)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52053259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52053259, 1)] : List FactorBlock).map factorBlockValue).prod) = 208213037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_52053259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 208213037) ^ 104106518 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 208213037) ^ 4 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_218669401 : Nat.Prime 218669401 := by
  apply lucas_primality 218669401 (13 : ZMod 218669401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (41, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (41, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) = 218669401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_2963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 218669401) ^ 109334700 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 218669401) ^ 72889800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 218669401) ^ 43733880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 218669401) ^ 5333400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 218669401) ^ 73800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_225723599 : Nat.Prime 225723599 := by
  apply lucas_primality 225723599 (23 : ZMod 225723599)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (2624693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (2624693, 1)] : List FactorBlock).map factorBlockValue).prod) = 225723599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_2624693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 225723599) ^ 112861799 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (23 : ZMod 225723599) ^ 5249386 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (23 : ZMod 225723599) ^ 86 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_235379513 : Nat.Prime 235379513 := by
  apply lucas_primality 235379513 (3 : ZMod 235379513)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29422439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29422439, 1)] : List FactorBlock).map factorBlockValue).prod) = 235379513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_29422439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 235379513) ^ 117689756 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 235379513) ^ 8 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_252450449 : Nat.Prime 252450449 := by
  apply lucas_primality 252450449 (3 : ZMod 252450449)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (53, 2), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (53, 2), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 252450449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252450449) ^ 126225224 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 252450449) ^ 6157328 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 252450449) ^ 4763216 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 252450449) ^ 1842704 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_253747061 : Nat.Prime 253747061 := by
  apply lucas_primality 253747061 (2 : ZMod 253747061)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (929, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (929, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) = 253747061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_929
      · exact prime_fortySevenAS_1951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 253747061) ^ 126873530 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 253747061) ^ 50749412 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 253747061) ^ 36249580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 253747061) ^ 273140 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 253747061) ^ 130060 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_271415077 : Nat.Prime 271415077 := by
  apply lucas_primality 271415077 (2 : ZMod 271415077)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (1190417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (1190417, 1)] : List FactorBlock).map factorBlockValue).prod) = 271415077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_1190417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 271415077) ^ 135707538 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 271415077) ^ 90471692 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 271415077) ^ 14285004 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 271415077) ^ 228 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_291431957 : Nat.Prime 291431957 := by
  apply lucas_primality 291431957 (2 : ZMod 291431957)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3834631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3834631, 1)] : List FactorBlock).map factorBlockValue).prod) = 291431957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_3834631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 291431957) ^ 145715978 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 291431957) ^ 15338524 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 291431957) ^ 76 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_327826819 : Nat.Prime 327826819 := by
  apply lucas_primality 327826819 (3 : ZMod 327826819)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (317, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (317, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 327826819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_317
      · exact prime_fortySevenAS_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 327826819) ^ 163913409 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 327826819) ^ 109275606 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 327826819) ^ 29802438 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 327826819) ^ 1034154 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 327826819) ^ 188298 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_387088069 : Nat.Prime 387088069 := by
  apply lucas_primality 387088069 (10 : ZMod 387088069)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1402493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1402493, 1)] : List FactorBlock).map factorBlockValue).prod) = 387088069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_1402493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 387088069) ^ 193544034 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 387088069) ^ 129029356 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 387088069) ^ 16829916 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 387088069) ^ 276 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_433231993 : Nat.Prime 433231993 := by
  apply lucas_primality 433231993 (5 : ZMod 433231993)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (6017111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (6017111, 1)] : List FactorBlock).map factorBlockValue).prod) = 433231993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_6017111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 433231993) ^ 216615996 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 433231993) ^ 144410664 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 433231993) ^ 72 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_440989739 : Nat.Prime 440989739 := by
  apply lucas_primality 440989739 (2 : ZMod 440989739)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31499267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31499267, 1)] : List FactorBlock).map factorBlockValue).prod) = 440989739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_31499267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 440989739) ^ 220494869 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 440989739) ^ 62998534 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 440989739) ^ 14 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_443824039 : Nat.Prime 443824039 := by
  apply lucas_primality 443824039 (6 : ZMod 443824039)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3522413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3522413, 1)] : List FactorBlock).map factorBlockValue).prod) = 443824039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_3522413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 443824039) ^ 221912019 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 443824039) ^ 147941346 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 443824039) ^ 63403434 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 443824039) ^ 126 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_452599661 : Nat.Prime 452599661 := by
  apply lucas_primality 452599661 (3 : ZMod 452599661)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (481489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (481489, 1)] : List FactorBlock).map factorBlockValue).prod) = 452599661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_481489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 452599661) ^ 226299830 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 452599661) ^ 90519932 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 452599661) ^ 9629780 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 452599661) ^ 940 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_592726819 : Nat.Prime 592726819 := by
  apply lucas_primality 592726819 (10 : ZMod 592726819)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (98787803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (98787803, 1)] : List FactorBlock).map factorBlockValue).prod) = 592726819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_98787803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 592726819) ^ 296363409 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 592726819) ^ 197575606 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 592726819) ^ 6 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_665386391 : Nat.Prime 665386391 := by
  apply lucas_primality 665386391 (13 : ZMod 665386391)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211, 1), (315349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211, 1), (315349, 1)] : List FactorBlock).map factorBlockValue).prod) = 665386391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_211
      · exact prime_fortySevenAS_315349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 665386391) ^ 332693195 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 665386391) ^ 133077278 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 665386391) ^ 3153490 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 665386391) ^ 2110 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_690934397 : Nat.Prime 690934397 := by
  apply lucas_primality 690934397 (2 : ZMod 690934397)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (277, 1), (21503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (277, 1), (21503, 1)] : List FactorBlock).map factorBlockValue).prod) = 690934397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_277
      · exact prime_fortySevenAS_21503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 690934397) ^ 345467198 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 690934397) ^ 23825324 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 690934397) ^ 2494348 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 690934397) ^ 32132 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_697335311 : Nat.Prime 697335311 := by
  apply lucas_primality 697335311 (7 : ZMod 697335311)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (101, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (101, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 697335311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_101
      · exact prime_fortySevenAS_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 697335311) ^ 348667655 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 697335311) ^ 139467062 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 697335311) ^ 99619330 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 697335311) ^ 13157270 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 697335311) ^ 6904310 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 697335311) ^ 374710 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_804701701 : Nat.Prime 804701701 := by
  apply lucas_primality 804701701 (2 : ZMod 804701701)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (11, 1), (81283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (11, 1), (81283, 1)] : List FactorBlock).map factorBlockValue).prod) = 804701701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_81283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 804701701) ^ 402350850 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 804701701) ^ 268233900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 804701701) ^ 160940340 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 804701701) ^ 73154700 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 804701701) ^ 9900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_822010181 : Nat.Prime 822010181 := by
  apply lucas_primality 822010181 (7 : ZMod 822010181)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (1423, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (1423, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 822010181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_1423
      · exact prime_fortySevenAS_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 822010181) ^ 411005090 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 822010181) ^ 164402036 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 822010181) ^ 48353540 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 822010181) ^ 577660 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 822010181) ^ 483820 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_837305507 : Nat.Prime 837305507 := by
  apply lucas_primality 837305507 (2 : ZMod 837305507)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1049, 1), (399097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1049, 1), (399097, 1)] : List FactorBlock).map factorBlockValue).prod) = 837305507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_1049
      · exact prime_fortySevenAS_399097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 837305507) ^ 418652753 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 837305507) ^ 798194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 837305507) ^ 2098 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_903140527 : Nat.Prime 903140527 := by
  apply lucas_primality 903140527 (3 : ZMod 903140527)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (309083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (309083, 1)] : List FactorBlock).map factorBlockValue).prod) = 903140527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_487
      · exact prime_fortySevenAS_309083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 903140527) ^ 451570263 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 903140527) ^ 301046842 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 903140527) ^ 1854498 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 903140527) ^ 2922 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1075142701 : Nat.Prime 1075142701 := by
  apply lucas_primality 1075142701 (2 : ZMod 1075142701)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (491, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (491, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1075142701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_491
      · exact prime_fortySevenAS_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1075142701) ^ 537571350 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1075142701) ^ 358380900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1075142701) ^ 215028540 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1075142701) ^ 2189700 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1075142701) ^ 1325700 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1182909643 : Nat.Prime 1182909643 := by
  apply lucas_primality 1182909643 (2 : ZMod 1182909643)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (8571809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (8571809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182909643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_8571809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1182909643) ^ 591454821 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182909643) ^ 394303214 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182909643) ^ 51430854 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182909643) ^ 138 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_113
      · exact prime_fortySevenAS_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1510405709 : Nat.Prime 1510405709 := by
  apply lucas_primality 1510405709 (2 : ZMod 1510405709)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1249, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1249, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510405709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_1249
      · exact prime_fortySevenAS_43189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1510405709) ^ 755202854 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510405709) ^ 215772244 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510405709) ^ 1209292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1510405709) ^ 34972 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1580699557 : Nat.Prime 1580699557 := by
  apply lucas_primality 1580699557 (2 : ZMod 1580699557)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (14636107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (14636107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1580699557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_14636107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1580699557) ^ 790349778 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1580699557) ^ 526899852 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1580699557) ^ 108 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1605714247 : Nat.Prime 1605714247 := by
  apply lucas_primality 1605714247 (3 : ZMod 1605714247)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29735449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29735449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1605714247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_29735449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1605714247) ^ 802857123 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605714247) ^ 535238082 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605714247) ^ 54 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1682320103 : Nat.Prime 1682320103 := by
  apply lucas_primality 1682320103 (5 : ZMod 1682320103)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (283, 1), (6029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (283, 1), (6029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682320103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_283
      · exact prime_fortySevenAS_6029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1682320103) ^ 841160051 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1682320103) ^ 98960006 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1682320103) ^ 58011038 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1682320103) ^ 5944594 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1682320103) ^ 279038 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1805788793 : Nat.Prime 1805788793 := by
  apply lucas_primality 1805788793 (3 : ZMod 1805788793)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (225723599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (225723599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1805788793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_225723599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1805788793) ^ 902894396 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1805788793) ^ 8 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1965060523 : Nat.Prime 1965060523 := by
  apply lucas_primality 1965060523 (2 : ZMod 1965060523)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (23, 1), (131, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (23, 1), (131, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1965060523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_131
      · exact prime_fortySevenAS_1907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1965060523) ^ 982530261 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965060523) ^ 655020174 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965060523) ^ 103424238 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965060523) ^ 85437414 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965060523) ^ 15000462 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965060523) ^ 1030446 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2052016643 : Nat.Prime 2052016643 := by
  apply lucas_primality 2052016643 (2 : ZMod 2052016643)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (367, 1), (215051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (367, 1), (215051, 1)] : List FactorBlock).map factorBlockValue).prod) = 2052016643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_367
      · exact prime_fortySevenAS_215051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2052016643) ^ 1026008321 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2052016643) ^ 157847434 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2052016643) ^ 5591326 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2052016643) ^ 9542 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2083815089 : Nat.Prime 2083815089 := by
  apply lucas_primality 2083815089 (3 : ZMod 2083815089)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (43, 1), (131687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (43, 1), (131687, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083815089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_131687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2083815089) ^ 1041907544 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2083815089) ^ 90600656 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2083815089) ^ 48460816 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2083815089) ^ 15824 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2103735713 : Nat.Prime 2103735713 := by
  apply lucas_primality 2103735713 (5 : ZMod 2103735713)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (1433, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (1433, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103735713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_1433
      · exact prime_fortySevenAS_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2103735713) ^ 1051867856 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2103735713) ^ 161825824 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2103735713) ^ 1468064 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2103735713) ^ 596128 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2403497713 : Nat.Prime 2403497713 := by
  apply lucas_primality 2403497713 (5 : ZMod 2403497713)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (197, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (197, 1), (3301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2403497713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_197
      · exact prime_fortySevenAS_3301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2403497713) ^ 1201748856 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403497713) ^ 801165904 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403497713) ^ 343356816 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403497713) ^ 218499792 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403497713) ^ 12200496 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 2403497713) ^ 728112 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2407689551 : Nat.Prime 2407689551 := by
  apply lucas_primality 2407689551 (7 : ZMod 2407689551)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (6879113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (6879113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2407689551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_6879113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2407689551) ^ 1203844775 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 2407689551) ^ 481537910 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 2407689551) ^ 343955650 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 2407689551) ^ 350 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2683619707 : Nat.Prime 2683619707 := by
  apply lucas_primality 2683619707 (2 : ZMod 2683619707)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (4180093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (4180093, 1)] : List FactorBlock).map factorBlockValue).prod) = 2683619707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_107
      · exact prime_fortySevenAS_4180093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2683619707) ^ 1341809853 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2683619707) ^ 894539902 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2683619707) ^ 25080558 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2683619707) ^ 642 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_3921841397 : Nat.Prime 3921841397 := by
  apply lucas_primality 3921841397 (2 : ZMod 3921841397)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (89132759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (89132759, 1)] : List FactorBlock).map factorBlockValue).prod) = 3921841397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_89132759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3921841397) ^ 1960920698 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 3921841397) ^ 356531036 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 3921841397) ^ 44 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4040990453 : Nat.Prime 4040990453 := by
  apply lucas_primality 4040990453 (3 : ZMod 4040990453)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (53170927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (53170927, 1)] : List FactorBlock).map factorBlockValue).prod) = 4040990453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_53170927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4040990453) ^ 2020495226 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4040990453) ^ 212683708 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4040990453) ^ 76 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4105153097 : Nat.Prime 4105153097 := by
  apply lucas_primality 4105153097 (3 : ZMod 4105153097)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (46649467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (46649467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4105153097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_46649467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4105153097) ^ 2052576548 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105153097) ^ 373195736 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4105153097) ^ 88 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4193206057 : Nat.Prime 4193206057 := by
  apply lucas_primality 4193206057 (5 : ZMod 4193206057)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (13, 1), (277, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (13, 1), (277, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 4193206057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_277
      · exact prime_fortySevenAS_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4193206057) ^ 2096603028 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 4193206057) ^ 1397735352 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 4193206057) ^ 322554312 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 4193206057) ^ 15137928 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 4193206057) ^ 7000344 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4474637801 : Nat.Prime 4474637801 := by
  apply lucas_primality 4474637801 (3 : ZMod 4474637801)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (22373189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (22373189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4474637801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_22373189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4474637801) ^ 2237318900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474637801) ^ 894927560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4474637801) ^ 200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4815379103 : Nat.Prime 4815379103 := by
  apply lucas_primality 4815379103 (5 : ZMod 4815379103)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2407689551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2407689551, 1)] : List FactorBlock).map factorBlockValue).prod) = 4815379103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_2407689551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4815379103) ^ 2407689551 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 4815379103) ^ 2 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5119487069 : Nat.Prime 5119487069 := by
  apply lucas_primality 5119487069 (2 : ZMod 5119487069)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (6496811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (6496811, 1)] : List FactorBlock).map factorBlockValue).prod) = 5119487069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_197
      · exact prime_fortySevenAS_6496811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5119487069) ^ 2559743534 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5119487069) ^ 25987244 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5119487069) ^ 788 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5170965281 : Nat.Prime 5170965281 := by
  apply lucas_primality 5170965281 (3 : ZMod 5170965281)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (2486041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (2486041, 1)] : List FactorBlock).map factorBlockValue).prod) = 5170965281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_2486041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5170965281) ^ 2585482640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5170965281) ^ 1034193056 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5170965281) ^ 397766560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5170965281) ^ 2080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5482504763 : Nat.Prime 5482504763 := by
  apply lucas_primality 5482504763 (2 : ZMod 5482504763)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2203, 1), (177761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2203, 1), (177761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5482504763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_2203
      · exact prime_fortySevenAS_177761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5482504763) ^ 2741252381 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5482504763) ^ 783214966 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5482504763) ^ 2488654 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5482504763) ^ 30842 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5578682489 : Nat.Prime 5578682489 := by
  apply lucas_primality 5578682489 (3 : ZMod 5578682489)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (697335311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (697335311, 1)] : List FactorBlock).map factorBlockValue).prod) = 5578682489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_697335311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5578682489) ^ 2789341244 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5578682489) ^ 8 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5887336927 : Nat.Prime 5887336927 := by
  apply lucas_primality 5887336927 (3 : ZMod 5887336927)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23599, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23599, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) = 5887336927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23599
      · exact prime_fortySevenAS_41579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5887336927) ^ 2943668463 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5887336927) ^ 1962445642 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5887336927) ^ 249474 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5887336927) ^ 141594 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_6122743229 : Nat.Prime 6122743229 := by
  apply lucas_primality 6122743229 (2 : ZMod 6122743229)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (218669401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (218669401, 1)] : List FactorBlock).map factorBlockValue).prod) = 6122743229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_218669401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6122743229) ^ 3061371614 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122743229) ^ 874677604 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122743229) ^ 28 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_6682022579 : Nat.Prime 6682022579 := by
  apply lucas_primality 6682022579 (6 : ZMod 6682022579)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (43389757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (43389757, 1)] : List FactorBlock).map factorBlockValue).prod) = 6682022579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_43389757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6682022579) ^ 3341011289 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 6682022579) ^ 954574654 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 6682022579) ^ 607456598 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 6682022579) ^ 154 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_6967585243 : Nat.Prime 6967585243 := by
  apply lucas_primality 6967585243 (2 : ZMod 6967585243)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (387088069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (387088069, 1)] : List FactorBlock).map factorBlockValue).prod) = 6967585243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_387088069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6967585243) ^ 3483792621 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967585243) ^ 2322528414 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967585243) ^ 18 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_7614196531 : Nat.Prime 7614196531 := by
  apply lucas_primality 7614196531 (7 : ZMod 7614196531)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (389, 1), (7331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (389, 1), (7331, 1)] : List FactorBlock).map factorBlockValue).prod) = 7614196531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_89
      · exact prime_fortySevenAS_389
      · exact prime_fortySevenAS_7331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7614196531) ^ 3807098265 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 7614196531) ^ 2538065510 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 7614196531) ^ 1522839306 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 7614196531) ^ 85552770 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 7614196531) ^ 19573770 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 7614196531) ^ 1038630 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_9145156117 : Nat.Prime 9145156117 := by
  apply lucas_primality 9145156117 (2 : ZMod 9145156117)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (3929, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (3929, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) = 9145156117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_3929
      · exact prime_fortySevenAS_6257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9145156117) ^ 4572578058 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145156117) ^ 3048385372 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145156117) ^ 295005036 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145156117) ^ 2327604 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 9145156117) ^ 1461588 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_11172970381 : Nat.Prime 11172970381 := by
  apply lucas_primality 11172970381 (2 : ZMod 11172970381)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (71, 1), (18341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (71, 1), (18341, 1)] : List FactorBlock).map factorBlockValue).prod) = 11172970381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_71
      · exact prime_fortySevenAS_18341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11172970381) ^ 5586485190 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 3724323460 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 2234594076 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 1015724580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 859459260 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 157365780 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172970381) ^ 609180 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_11790363139 : Nat.Prime 11790363139 := by
  apply lucas_primality 11790363139 (2 : ZMod 11790363139)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1965060523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1965060523, 1)] : List FactorBlock).map factorBlockValue).prod) = 11790363139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_1965060523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11790363139) ^ 5895181569 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11790363139) ^ 3930121046 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 11790363139) ^ 6 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_12455169721 : Nat.Prime 12455169721 := by
  apply lucas_primality 12455169721 (13 : ZMod 12455169721)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (14827583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (14827583, 1)] : List FactorBlock).map factorBlockValue).prod) = 12455169721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_14827583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12455169721) ^ 6227584860 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 12455169721) ^ 4151723240 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 12455169721) ^ 2491033944 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 12455169721) ^ 1779309960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 12455169721) ^ 840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_12599143847 : Nat.Prime 12599143847 := by
  apply lucas_primality 12599143847 (5 : ZMod 12599143847)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (89, 1), (449, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (89, 1), (449, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) = 12599143847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_89
      · exact prime_fortySevenAS_449
      · exact prime_fortySevenAS_8297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12599143847) ^ 6299571923 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12599143847) ^ 663112834 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12599143847) ^ 141563414 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12599143847) ^ 28060454 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12599143847) ^ 1518518 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_12706130617 : Nat.Prime 12706130617 := by
  apply lucas_primality 12706130617 (5 : ZMod 12706130617)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (31142477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (31142477, 1)] : List FactorBlock).map factorBlockValue).prod) = 12706130617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_31142477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12706130617) ^ 6353065308 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12706130617) ^ 4235376872 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12706130617) ^ 747419448 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 12706130617) ^ 408 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_15750841357 : Nat.Prime 15750841357 := by
  apply lucas_primality 15750841357 (5 : ZMod 15750841357)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (251, 1), (24551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (251, 1), (24551, 1)] : List FactorBlock).map factorBlockValue).prod) = 15750841357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_71
      · exact prime_fortySevenAS_251
      · exact prime_fortySevenAS_24551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15750841357) ^ 7875420678 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 15750841357) ^ 5250280452 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 15750841357) ^ 221842836 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 15750841357) ^ 62752356 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 15750841357) ^ 641556 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_16160852801 : Nat.Prime 16160852801 := by
  apply lucas_primality 16160852801 (6 : ZMod 16160852801)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (17, 1), (19, 1), (31271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (17, 1), (19, 1), (31271, 1)] : List FactorBlock).map factorBlockValue).prod) = 16160852801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_31271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16160852801) ^ 8080426400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 16160852801) ^ 3232170560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 16160852801) ^ 950638400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 16160852801) ^ 850571200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 16160852801) ^ 516800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_16389849299 : Nat.Prime 16389849299 := by
  apply lucas_primality 16389849299 (2 : ZMod 16389849299)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (12457, 1), (15299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (12457, 1), (15299, 1)] : List FactorBlock).map factorBlockValue).prod) = 16389849299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_12457
      · exact prime_fortySevenAS_15299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16389849299) ^ 8194924649 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 16389849299) ^ 381159286 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 16389849299) ^ 1315714 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 16389849299) ^ 1071302 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_19706328241 : Nat.Prime 19706328241 := by
  apply lucas_primality 19706328241 (13 : ZMod 19706328241)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23, 1), (29, 1), (257, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23, 1), (29, 1), (257, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 19706328241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_257
      · exact prime_fortySevenAS_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 19706328241) ^ 9853164120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 6568776080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 3941265648 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 856796880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 679528560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 76678320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 19706328241) ^ 41140560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_25310612273 : Nat.Prime 25310612273 := by
  apply lucas_primality 25310612273 (3 : ZMod 25310612273)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (7568963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (7568963, 1)] : List FactorBlock).map factorBlockValue).prod) = 25310612273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_7568963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25310612273) ^ 12655306136 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 25310612273) ^ 2300964752 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 25310612273) ^ 1332137488 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 25310612273) ^ 3344 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_28892434861 : Nat.Prime 28892434861 := by
  apply lucas_primality 28892434861 (2 : ZMod 28892434861)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (23, 1), (2326283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (23, 1), (2326283, 1)] : List FactorBlock).map factorBlockValue).prod) = 28892434861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_2326283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28892434861) ^ 14446217430 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28892434861) ^ 9630811620 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28892434861) ^ 5778486972 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28892434861) ^ 1256192820 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28892434861) ^ 12420 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_29987302253 : Nat.Prime 29987302253 := by
  apply lucas_primality 29987302253 (2 : ZMod 29987302253)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (440989739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (440989739, 1)] : List FactorBlock).map factorBlockValue).prod) = 29987302253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_440989739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29987302253) ^ 14993651126 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 29987302253) ^ 1763958956 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 29987302253) ^ 68 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_48981945833 : Nat.Prime 48981945833 := by
  apply lucas_primality 48981945833 (3 : ZMod 48981945833)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6122743229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6122743229, 1)] : List FactorBlock).map factorBlockValue).prod) = 48981945833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_6122743229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 48981945833) ^ 24490972916 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 48981945833) ^ 8 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_52963111757 : Nat.Prime 52963111757 := by
  apply lucas_primality 52963111757 (2 : ZMod 52963111757)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (229, 1), (1865161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (229, 1), (1865161, 1)] : List FactorBlock).map factorBlockValue).prod) = 52963111757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_229
      · exact prime_fortySevenAS_1865161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52963111757) ^ 26481555878 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 52963111757) ^ 1708487476 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 52963111757) ^ 231279964 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 52963111757) ^ 28396 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_53456180633 : Nat.Prime 53456180633 := by
  apply lucas_primality 53456180633 (3 : ZMod 53456180633)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6682022579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6682022579, 1)] : List FactorBlock).map factorBlockValue).prod) = 53456180633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_6682022579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 53456180633) ^ 26728090316 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 53456180633) ^ 8 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_59321812091 : Nat.Prime 59321812091 := by
  apply lucas_primality 59321812091 (2 : ZMod 59321812091)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1033, 1), (5742673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1033, 1), (5742673, 1)] : List FactorBlock).map factorBlockValue).prod) = 59321812091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_1033
      · exact prime_fortySevenAS_5742673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59321812091) ^ 29660906045 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 59321812091) ^ 11864362418 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 59321812091) ^ 57426730 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 59321812091) ^ 10330 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_67561755991 : Nat.Prime 67561755991 := by
  apply lucas_primality 67561755991 (6 : ZMod 67561755991)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (2767, 1), (17317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (2767, 1), (17317, 1)] : List FactorBlock).map factorBlockValue).prod) = 67561755991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_2767
      · exact prime_fortySevenAS_17317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67561755991) ^ 33780877995 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 67561755991) ^ 22520585330 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 67561755991) ^ 13512351198 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 67561755991) ^ 1437484170 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 67561755991) ^ 24416970 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 67561755991) ^ 3901470 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_97060803977 : Nat.Prime 97060803977 := by
  apply lucas_primality 97060803977 (3 : ZMod 97060803977)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (18127, 1), (669311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (18127, 1), (669311, 1)] : List FactorBlock).map factorBlockValue).prod) = 97060803977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_18127
      · exact prime_fortySevenAS_669311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 97060803977) ^ 48530401988 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 97060803977) ^ 5354488 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 97060803977) ^ 145016 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_98523674329 : Nat.Prime 98523674329 := by
  apply lucas_primality 98523674329 (17 : ZMod 98523674329)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4105153097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4105153097, 1)] : List FactorBlock).map factorBlockValue).prod) = 98523674329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_4105153097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 98523674329) ^ 49261837164 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 98523674329) ^ 32841224776 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 98523674329) ^ 24 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_100375518137 : Nat.Prime 100375518137 := by
  apply lucas_primality 100375518137 (3 : ZMod 100375518137)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (1877, 1), (80537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (1877, 1), (80537, 1)] : List FactorBlock).map factorBlockValue).prod) = 100375518137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_83
      · exact prime_fortySevenAS_1877
      · exact prime_fortySevenAS_80537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 100375518137) ^ 50187759068 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 100375518137) ^ 1209343592 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 100375518137) ^ 53476568 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 100375518137) ^ 1246328 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_100416284803 : Nat.Prime 100416284803 := by
  apply lucas_primality 100416284803 (2 : ZMod 100416284803)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5578682489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5578682489, 1)] : List FactorBlock).map factorBlockValue).prod) = 100416284803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5578682489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 100416284803) ^ 50208142401 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 100416284803) ^ 33472094934 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 100416284803) ^ 18 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_106299833741 : Nat.Prime 106299833741 := by
  apply lucas_primality 106299833741 (2 : ZMod 106299833741)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (547, 1), (9716621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (547, 1), (9716621, 1)] : List FactorBlock).map factorBlockValue).prod) = 106299833741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_547
      · exact prime_fortySevenAS_9716621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106299833741) ^ 53149916870 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 106299833741) ^ 21259966748 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 106299833741) ^ 194332420 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 106299833741) ^ 10940 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_110329362133 : Nat.Prime 110329362133 := by
  apply lucas_primality 110329362133 (5 : ZMod 110329362133)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 2), (293, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 2), (293, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) = 110329362133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_293
      · exact prime_fortySevenAS_1697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 110329362133) ^ 55164681066 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 110329362133) ^ 36776454044 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 110329362133) ^ 10029942012 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 110329362133) ^ 2690960052 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 110329362133) ^ 376550724 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 110329362133) ^ 65014356 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_142230192277 : Nat.Prime 142230192277 := by
  apply lucas_primality 142230192277 (5 : ZMod 142230192277)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (811, 1), (14614693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (811, 1), (14614693, 1)] : List FactorBlock).map factorBlockValue).prod) = 142230192277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_811
      · exact prime_fortySevenAS_14614693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 142230192277) ^ 71115096138 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 142230192277) ^ 47410064092 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 142230192277) ^ 175376316 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 142230192277) ^ 9732 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_149075044969 : Nat.Prime 149075044969 := by
  apply lucas_primality 149075044969 (17 : ZMod 149075044969)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (563, 1), (380441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (563, 1), (380441, 1)] : List FactorBlock).map factorBlockValue).prod) = 149075044969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_563
      · exact prime_fortySevenAS_380441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 149075044969) ^ 74537522484 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 149075044969) ^ 49691681656 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 149075044969) ^ 5140518792 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 149075044969) ^ 264786936 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 149075044969) ^ 391848 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_166540968017 : Nat.Prime 166540968017 := by
  apply lucas_primality 166540968017 (3 : ZMod 166540968017)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (15901, 1), (654601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (15901, 1), (654601, 1)] : List FactorBlock).map factorBlockValue).prod) = 166540968017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_15901
      · exact prime_fortySevenAS_654601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 166540968017) ^ 83270484008 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 166540968017) ^ 10473616 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 166540968017) ^ 254416 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_169617531497 : Nat.Prime 169617531497 := by
  apply lucas_primality 169617531497 (3 : ZMod 169617531497)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (1973, 1), (41491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (1973, 1), (41491, 1)] : List FactorBlock).map factorBlockValue).prod) = 169617531497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_1973
      · exact prime_fortySevenAS_41491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 169617531497) ^ 84808765748 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 169617531497) ^ 24231075928 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 169617531497) ^ 4584257608 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 169617531497) ^ 85969352 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 169617531497) ^ 4088056 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_179972301577 : Nat.Prime 179972301577 := by
  apply lucas_primality 179972301577 (7 : ZMod 179972301577)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (101, 1), (74245999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (101, 1), (74245999, 1)] : List FactorBlock).map factorBlockValue).prod) = 179972301577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_101
      · exact prime_fortySevenAS_74245999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 179972301577) ^ 89986150788 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 179972301577) ^ 59990767192 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 179972301577) ^ 1781903976 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 179972301577) ^ 2424 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_186954426157 : Nat.Prime 186954426157 := by
  apply lucas_primality 186954426157 (2 : ZMod 186954426157)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (709, 1), (467531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (709, 1), (467531, 1)] : List FactorBlock).map factorBlockValue).prod) = 186954426157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_709
      · exact prime_fortySevenAS_467531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186954426157) ^ 93477213078 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 186954426157) ^ 62318142052 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 186954426157) ^ 3977753748 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 186954426157) ^ 263687484 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 186954426157) ^ 399876 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_195942771331 : Nat.Prime 195942771331 := by
  apply lucas_primality 195942771331 (2 : ZMod 195942771331)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4513, 1), (1447247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4513, 1), (1447247, 1)] : List FactorBlock).map factorBlockValue).prod) = 195942771331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_4513
      · exact prime_fortySevenAS_1447247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 195942771331) ^ 97971385665 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 195942771331) ^ 65314257110 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 195942771331) ^ 39188554266 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 195942771331) ^ 43417410 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 195942771331) ^ 135390 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_258523477787 : Nat.Prime 258523477787 := by
  apply lucas_primality 258523477787 (2 : ZMod 258523477787)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (7669, 1), (55997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (7669, 1), (55997, 1)] : List FactorBlock).map factorBlockValue).prod) = 258523477787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_7669
      · exact prime_fortySevenAS_55997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 258523477787) ^ 129261738893 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 258523477787) ^ 36931925398 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 258523477787) ^ 6012173902 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 258523477787) ^ 33710194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 258523477787) ^ 4616738 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_312180710693 : Nat.Prime 312180710693 := by
  apply lucas_primality 312180710693 (2 : ZMod 312180710693)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163, 1), (757, 1), (632503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163, 1), (757, 1), (632503, 1)] : List FactorBlock).map factorBlockValue).prod) = 312180710693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_163
      · exact prime_fortySevenAS_757
      · exact prime_fortySevenAS_632503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 312180710693) ^ 156090355346 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 312180710693) ^ 1915219084 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 312180710693) ^ 412391956 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 312180710693) ^ 493564 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_412839599749 : Nat.Prime 412839599749 := by
  apply lucas_primality 412839599749 (2 : ZMod 412839599749)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (150232751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (150232751, 1)] : List FactorBlock).map factorBlockValue).prod) = 412839599749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_229
      · exact prime_fortySevenAS_150232751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 412839599749) ^ 206419799874 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 412839599749) ^ 137613199916 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 412839599749) ^ 1802793012 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 412839599749) ^ 2748 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_397
      · exact prime_fortySevenAS_2531
      · exact prime_fortySevenAS_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_587783349997 : Nat.Prime 587783349997 := by
  apply lucas_primality 587783349997 (5 : ZMod 587783349997)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (48981945833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (48981945833, 1)] : List FactorBlock).map factorBlockValue).prod) = 587783349997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_48981945833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 587783349997) ^ 293891674998 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 587783349997) ^ 195927783332 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 587783349997) ^ 12 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_910102790251 : Nat.Prime 910102790251 := by
  apply lucas_primality 910102790251 (2 : ZMod 910102790251)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 3), (17, 1), (7931179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 3), (17, 1), (7931179, 1)] : List FactorBlock).map factorBlockValue).prod) = 910102790251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_7931179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 910102790251) ^ 455051395125 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 910102790251) ^ 303367596750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 910102790251) ^ 182020558050 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 910102790251) ^ 53535458250 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 910102790251) ^ 114750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_984582953813 : Nat.Prime 984582953813 := by
  apply lucas_primality 984582953813 (2 : ZMod 984582953813)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (33311, 1), (71741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (33311, 1), (71741, 1)] : List FactorBlock).map factorBlockValue).prod) = 984582953813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_103
      · exact prime_fortySevenAS_33311
      · exact prime_fortySevenAS_71741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 984582953813) ^ 492291476906 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 984582953813) ^ 9559057804 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 984582953813) ^ 29557292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 984582953813) ^ 13724132 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1180745678779 : Nat.Prime 1180745678779 := by
  apply lucas_primality 1180745678779 (2 : ZMod 1180745678779)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (2767, 1), (313307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (2767, 1), (313307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180745678779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_227
      · exact prime_fortySevenAS_2767
      · exact prime_fortySevenAS_313307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1180745678779) ^ 590372839389 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180745678779) ^ 393581892926 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180745678779) ^ 5201522814 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180745678779) ^ 426724134 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180745678779) ^ 3768654 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1216111607839 : Nat.Prime 1216111607839 := by
  apply lucas_primality 1216111607839 (6 : ZMod 1216111607839)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67561755991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67561755991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1216111607839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_67561755991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1216111607839) ^ 608055803919 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1216111607839) ^ 405370535946 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1216111607839) ^ 18 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1341052665409 : Nat.Prime 1341052665409 := by
  apply lucas_primality 1341052665409 (11 : ZMod 1341052665409)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (19, 2), (67, 1), (96259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (19, 2), (67, 1), (96259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1341052665409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_67
      · exact prime_fortySevenAS_96259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1341052665409) ^ 670526332704 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 1341052665409) ^ 447017555136 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 1341052665409) ^ 70581719232 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 1341052665409) ^ 20015711424 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 1341052665409) ^ 13931712 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_35279
      · exact prime_fortySevenAS_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1557255003763 : Nat.Prime 1557255003763 := by
  apply lucas_primality 1557255003763 (2 : ZMod 1557255003763)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (991, 1), (11386939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (991, 1), (11386939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1557255003763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_991
      · exact prime_fortySevenAS_11386939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1557255003763) ^ 778627501881 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557255003763) ^ 519085001254 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557255003763) ^ 67706739294 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557255003763) ^ 1571397582 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1557255003763) ^ 136758 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1630041108313 : Nat.Prime 1630041108313 := by
  apply lucas_primality 1630041108313 (10 : ZMod 1630041108313)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (101363, 1), (670051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (101363, 1), (670051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630041108313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_101363
      · exact prime_fortySevenAS_670051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1630041108313) ^ 815020554156 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1630041108313) ^ 543347036104 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1630041108313) ^ 16081224 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1630041108313) ^ 2432712 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2172812415463 : Nat.Prime 2172812415463 := by
  apply lucas_primality 2172812415463 (3 : ZMod 2172812415463)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (3001, 1), (79337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (3001, 1), (79337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2172812415463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_3001
      · exact prime_fortySevenAS_79337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2172812415463) ^ 1086406207731 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2172812415463) ^ 724270805154 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2172812415463) ^ 167139416574 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2172812415463) ^ 724029462 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2172812415463) ^ 27387126 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2760060169439 : Nat.Prime 2760060169439 := by
  apply lucas_primality 2760060169439 (11 : ZMod 2760060169439)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (41, 1), (235379513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (41, 1), (235379513, 1)] : List FactorBlock).map factorBlockValue).prod) = 2760060169439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_235379513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2760060169439) ^ 1380030084719 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 2760060169439) ^ 250914560858 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 2760060169439) ^ 212312320726 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 2760060169439) ^ 67318540718 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 2760060169439) ^ 11726 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2896074053861 : Nat.Prime 2896074053861 := by
  apply lucas_primality 2896074053861 (2 : ZMod 2896074053861)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (8447, 1), (1318663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (8447, 1), (1318663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2896074053861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_8447
      · exact prime_fortySevenAS_1318663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2896074053861) ^ 1448037026930 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2896074053861) ^ 579214810772 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2896074053861) ^ 222774927220 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2896074053861) ^ 342852380 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2896074053861) ^ 2196220 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_3037935340673 : Nat.Prime 3037935340673 := by
  apply lucas_primality 3037935340673 (3 : ZMod 3037935340673)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (131, 1), (181174579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (131, 1), (181174579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3037935340673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_131
      · exact prime_fortySevenAS_181174579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3037935340673) ^ 1518967670336 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 3037935340673) ^ 23190346112 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 3037935340673) ^ 16768 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4108225691527 : Nat.Prime 4108225691527 := by
  apply lucas_primality 4108225691527 (3 : ZMod 4108225691527)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (1682320103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (1682320103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4108225691527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_1682320103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4108225691527) ^ 2054112845763 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4108225691527) ^ 1369408563842 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4108225691527) ^ 373475062866 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4108225691527) ^ 111033126798 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4108225691527) ^ 2442 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4264667808833 : Nat.Prime 4264667808833 := by
  apply lucas_primality 4264667808833 (3 : ZMod 4264667808833)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (643, 1), (809, 1), (128099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (643, 1), (809, 1), (128099, 1)] : List FactorBlock).map factorBlockValue).prod) = 4264667808833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_643
      · exact prime_fortySevenAS_809
      · exact prime_fortySevenAS_128099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4264667808833) ^ 2132333904416 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4264667808833) ^ 6632453824 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4264667808833) ^ 5271530048 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 4264667808833) ^ 33291968 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4448493112031 : Nat.Prime 4448493112031 := by
  apply lucas_primality 4448493112031 (13 : ZMod 4448493112031)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (149, 1), (271415077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (149, 1), (271415077, 1)] : List FactorBlock).map factorBlockValue).prod) = 4448493112031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_149
      · exact prime_fortySevenAS_271415077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4448493112031) ^ 2224246556015 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 4448493112031) ^ 889698622406 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 4448493112031) ^ 404408464730 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 4448493112031) ^ 29855658470 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 4448493112031) ^ 16390 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5883978837713 : Nat.Prime 5883978837713 := by
  apply lucas_primality 5883978837713 (3 : ZMod 5883978837713)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (457, 1), (804701701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (457, 1), (804701701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5883978837713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_457
      · exact prime_fortySevenAS_804701701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5883978837713) ^ 2941989418856 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5883978837713) ^ 12875227216 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 5883978837713) ^ 7312 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_9101027902511 : Nat.Prime 9101027902511 := by
  apply lucas_primality 9101027902511 (17 : ZMod 9101027902511)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (910102790251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (910102790251, 1)] : List FactorBlock).map factorBlockValue).prod) = 9101027902511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_910102790251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 9101027902511) ^ 4550513951255 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 9101027902511) ^ 1820205580502 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (17 : ZMod 9101027902511) ^ 10 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_9281997862381 : Nat.Prime 9281997862381 := by
  apply lucas_primality 9281997862381 (11 : ZMod 9281997862381)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (619, 1), (8011, 1), (10399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (619, 1), (8011, 1), (10399, 1)] : List FactorBlock).map factorBlockValue).prod) = 9281997862381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_619
      · exact prime_fortySevenAS_8011
      · exact prime_fortySevenAS_10399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9281997862381) ^ 4640998931190 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 9281997862381) ^ 3093999287460 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 9281997862381) ^ 1856399572476 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 9281997862381) ^ 14995150020 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 9281997862381) ^ 1158656580 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 9281997862381) ^ 892585620 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_11217265569421 : Nat.Prime 11217265569421 := by
  apply lucas_primality 11217265569421 (6 : ZMod 11217265569421)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (186954426157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (186954426157, 1)] : List FactorBlock).map factorBlockValue).prod) = 11217265569421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_186954426157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11217265569421) ^ 5608632784710 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 11217265569421) ^ 3739088523140 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 11217265569421) ^ 2243453113884 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 11217265569421) ^ 60 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_12525797621219 : Nat.Prime 12525797621219 := by
  apply lucas_primality 12525797621219 (2 : ZMod 12525797621219)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1399, 1), (91361159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1399, 1), (91361159, 1)] : List FactorBlock).map factorBlockValue).prod) = 12525797621219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_1399
      · exact prime_fortySevenAS_91361159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12525797621219) ^ 6262898810609 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 12525797621219) ^ 1789399660174 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 12525797621219) ^ 8953393582 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 12525797621219) ^ 137102 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_13735951270493 : Nat.Prime 13735951270493 := by
  apply lucas_primality 13735951270493 (2 : ZMod 13735951270493)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (312180710693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (312180710693, 1)] : List FactorBlock).map factorBlockValue).prod) = 13735951270493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_312180710693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13735951270493) ^ 6867975635246 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 13735951270493) ^ 1248722842772 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 13735951270493) ^ 44 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_15901696384003 : Nat.Prime 15901696384003 := by
  apply lucas_primality 15901696384003 (2 : ZMod 15901696384003)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (13, 1), (37, 1), (401, 1), (138793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (13, 1), (37, 1), (401, 1), (138793, 1)] : List FactorBlock).map factorBlockValue).prod) = 15901696384003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_401
      · exact prime_fortySevenAS_138793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15901696384003) ^ 7950848192001 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 5300565461334 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 1445608762182 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 1223207414154 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 429775577946 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 39655103202 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 15901696384003) ^ 114571314 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_17258159368267 : Nat.Prime 17258159368267 := by
  apply lucas_primality 17258159368267 (3 : ZMod 17258159368267)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (181, 1), (690934397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (181, 1), (690934397, 1)] : List FactorBlock).map factorBlockValue).prod) = 17258159368267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_181
      · exact prime_fortySevenAS_690934397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17258159368267) ^ 8629079684133 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 17258159368267) ^ 5752719789422 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 17258159368267) ^ 750354755142 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 17258159368267) ^ 95348946786 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 17258159368267) ^ 24978 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_18921397311083 : Nat.Prime 18921397311083 := by
  apply lucas_primality 18921397311083 (2 : ZMod 18921397311083)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (673, 1), (5297, 1), (379123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (673, 1), (5297, 1), (379123, 1)] : List FactorBlock).map factorBlockValue).prod) = 18921397311083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_673
      · exact prime_fortySevenAS_5297
      · exact prime_fortySevenAS_379123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18921397311083) ^ 9460698655541 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18921397311083) ^ 2703056758726 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18921397311083) ^ 28115003434 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18921397311083) ^ 3572096906 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18921397311083) ^ 49908334 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_20038412542721 : Nat.Prime 20038412542721 := by
  apply lucas_primality 20038412542721 (3 : ZMod 20038412542721)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (11, 1), (13, 1), (79, 1), (1385767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (11, 1), (13, 1), (79, 1), (1385767, 1)] : List FactorBlock).map factorBlockValue).prod) = 20038412542721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_79
      · exact prime_fortySevenAS_1385767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20038412542721) ^ 10019206271360 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 20038412542721) ^ 4007682508544 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 20038412542721) ^ 1821673867520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 20038412542721) ^ 1541416349440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 20038412542721) ^ 253650791680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 20038412542721) ^ 14460160 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_25976404933139 : Nat.Prime 25976404933139 := by
  apply lucas_primality 25976404933139 (2 : ZMod 25976404933139)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1180745678779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1180745678779, 1)] : List FactorBlock).map factorBlockValue).prod) = 25976404933139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_1180745678779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25976404933139) ^ 12988202466569 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 25976404933139) ^ 2361491357558 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 25976404933139) ^ 22 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_28980918557501 : Nat.Prime 28980918557501 := by
  apply lucas_primality 28980918557501 (2 : ZMod 28980918557501)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (7, 2), (13, 1), (18198379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (7, 2), (13, 1), (18198379, 1)] : List FactorBlock).map factorBlockValue).prod) = 28980918557501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_18198379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28980918557501) ^ 14490459278750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28980918557501) ^ 5796183711500 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28980918557501) ^ 4140131222500 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28980918557501) ^ 2229301427500 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 28980918557501) ^ 1592500 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_30367437039077 : Nat.Prime 30367437039077 := by
  apply lucas_primality 30367437039077 (3 : ZMod 30367437039077)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (9829, 1), (1465643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (9829, 1), (1465643, 1)] : List FactorBlock).map factorBlockValue).prod) = 30367437039077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_9829
      · exact prime_fortySevenAS_1465643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30367437039077) ^ 15183718519538 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 30367437039077) ^ 1786319825828 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 30367437039077) ^ 979594743196 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 30367437039077) ^ 3089575444 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 30367437039077) ^ 20719532 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_38640842372147 : Nat.Prime 38640842372147 := by
  apply lucas_primality 38640842372147 (2 : ZMod 38640842372147)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2760060169439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2760060169439, 1)] : List FactorBlock).map factorBlockValue).prod) = 38640842372147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_2760060169439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38640842372147) ^ 19320421186073 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 38640842372147) ^ 5520120338878 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 38640842372147) ^ 14 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_48715072770383 : Nat.Prime 48715072770383 := by
  apply lucas_primality 48715072770383 (5 : ZMod 48715072770383)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (412839599749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (412839599749, 1)] : List FactorBlock).map factorBlockValue).prod) = 48715072770383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_412839599749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48715072770383) ^ 24357536385191 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 48715072770383) ^ 825679199498 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 48715072770383) ^ 118 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_52385523976447 : Nat.Prime 52385523976447 := by
  apply lucas_primality 52385523976447 (5 : ZMod 52385523976447)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1483, 1), (5887336927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1483, 1), (5887336927, 1)] : List FactorBlock).map factorBlockValue).prod) = 52385523976447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_1483
      · exact prime_fortySevenAS_5887336927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52385523976447) ^ 26192761988223 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 52385523976447) ^ 17461841325482 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 52385523976447) ^ 35324021562 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 52385523976447) ^ 8898 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_59705349323663 : Nat.Prime 59705349323663 := by
  apply lucas_primality 59705349323663 (5 : ZMod 59705349323663)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4264667808833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4264667808833, 1)] : List FactorBlock).map factorBlockValue).prod) = 59705349323663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_4264667808833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 59705349323663) ^ 29852674661831 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 59705349323663) ^ 8529335617666 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 59705349323663) ^ 14 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_75821647671247 : Nat.Prime 75821647671247 := by
  apply lucas_primality 75821647671247 (5 : ZMod 75821647671247)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (59, 1), (12599143847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (59, 1), (12599143847, 1)] : List FactorBlock).map factorBlockValue).prod) = 75821647671247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_12599143847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 75821647671247) ^ 37910823835623 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 75821647671247) ^ 25273882557082 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 75821647671247) ^ 4460096921838 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 75821647671247) ^ 1285112672394 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 75821647671247) ^ 6018 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_78195856452211 : Nat.Prime 78195856452211 := by
  apply lucas_primality 78195856452211 (3 : ZMod 78195856452211)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (59, 1), (2103735713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (59, 1), (2103735713, 1)] : List FactorBlock).map factorBlockValue).prod) = 78195856452211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_2103735713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78195856452211) ^ 39097928226105 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 78195856452211) ^ 26065285484070 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 78195856452211) ^ 15639171290442 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 78195856452211) ^ 11170836636030 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 78195856452211) ^ 1325353499190 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 78195856452211) ^ 37170 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_90296476324529 : Nat.Prime 90296476324529 := by
  apply lucas_primality 90296476324529 (3 : ZMod 90296476324529)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1439, 1), (3921841397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1439, 1), (3921841397, 1)] : List FactorBlock).map factorBlockValue).prod) = 90296476324529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_1439
      · exact prime_fortySevenAS_3921841397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 90296476324529) ^ 45148238162264 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 90296476324529) ^ 62749462352 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 90296476324529) ^ 23024 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_112763034898627 : Nat.Prime 112763034898627 := by
  apply lucas_primality 112763034898627 (2 : ZMod 112763034898627)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (331, 1), (16369, 1), (495527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (331, 1), (16369, 1), (495527, 1)] : List FactorBlock).map factorBlockValue).prod) = 112763034898627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_331
      · exact prime_fortySevenAS_16369
      · exact prime_fortySevenAS_495527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112763034898627) ^ 56381517449313 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 112763034898627) ^ 37587678299542 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 112763034898627) ^ 16109004985518 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 112763034898627) ^ 340673821446 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 112763034898627) ^ 6888816354 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 112763034898627) ^ 227561838 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_124157088634487 : Nat.Prime 124157088634487 := by
  apply lucas_primality 124157088634487 (5 : ZMod 124157088634487)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (263, 1), (7614196531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (263, 1), (7614196531, 1)] : List FactorBlock).map factorBlockValue).prod) = 124157088634487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_263
      · exact prime_fortySevenAS_7614196531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124157088634487) ^ 62078544317243 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 124157088634487) ^ 4005067375306 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 124157088634487) ^ 472080184922 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 124157088634487) ^ 16306 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_192303317786903 : Nat.Prime 192303317786903 := by
  apply lucas_primality 192303317786903 (5 : ZMod 192303317786903)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13735951270493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13735951270493, 1)] : List FactorBlock).map factorBlockValue).prod) = 192303317786903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_13735951270493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 192303317786903) ^ 96151658893451 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 192303317786903) ^ 27471902540986 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 192303317786903) ^ 14 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_199863039150191 : Nat.Prime 199863039150191 := by
  apply lucas_primality 199863039150191 (7 : ZMod 199863039150191)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (167, 1), (49789, 1), (184901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (167, 1), (49789, 1), (184901, 1)] : List FactorBlock).map factorBlockValue).prod) = 199863039150191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_167
      · exact prime_fortySevenAS_49789
      · exact prime_fortySevenAS_184901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 199863039150191) ^ 99931519575095 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 199863039150191) ^ 39972607830038 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 199863039150191) ^ 15374079934630 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 199863039150191) ^ 1196784665570 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 199863039150191) ^ 4014200710 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 199863039150191) ^ 1080919190 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_256578315460729 : Nat.Prime 256578315460729 := by
  apply lucas_primality 256578315460729 (7 : ZMod 256578315460729)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (16067, 1), (665386391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (16067, 1), (665386391, 1)] : List FactorBlock).map factorBlockValue).prod) = 256578315460729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_16067
      · exact prime_fortySevenAS_665386391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 256578315460729) ^ 128289157730364 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 256578315460729) ^ 85526105153576 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 256578315460729) ^ 15969273384 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 256578315460729) ^ 385608 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_263458415475257 : Nat.Prime 263458415475257 := by
  apply lucas_primality 263458415475257 (3 : ZMod 263458415475257)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73, 1), (2377, 1), (4733, 1), (40099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73, 1), (2377, 1), (4733, 1), (40099, 1)] : List FactorBlock).map factorBlockValue).prod) = 263458415475257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_73
      · exact prime_fortySevenAS_2377
      · exact prime_fortySevenAS_4733
      · exact prime_fortySevenAS_40099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 263458415475257) ^ 131729207737628 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 263458415475257) ^ 3609019390072 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 263458415475257) ^ 110836523128 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 263458415475257) ^ 55664148632 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 263458415475257) ^ 6570199144 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_281784987228163 : Nat.Prime 281784987228163 := by
  apply lucas_primality 281784987228163 (2 : ZMod 281784987228163)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (73, 1), (1580699557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (73, 1), (1580699557, 1)] : List FactorBlock).map factorBlockValue).prod) = 281784987228163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_73
      · exact prime_fortySevenAS_1580699557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 281784987228163) ^ 140892493614081 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 281784987228163) ^ 93928329076054 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 281784987228163) ^ 25616817020742 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 281784987228163) ^ 7615810465626 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 281784987228163) ^ 3860068318194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 281784987228163) ^ 178266 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_436330881251113 : Nat.Prime 436330881251113 := by
  apply lucas_primality 436330881251113 (5 : ZMod 436330881251113)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (239, 1), (4474637801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (239, 1), (4474637801, 1)] : List FactorBlock).map factorBlockValue).prod) = 436330881251113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_239
      · exact prime_fortySevenAS_4474637801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 436330881251113) ^ 218165440625556 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 436330881251113) ^ 145443627083704 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 436330881251113) ^ 25666522426536 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 436330881251113) ^ 1825652222808 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 436330881251113) ^ 97512 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_485416005710533 : Nat.Prime 485416005710533 := by
  apply lucas_primality 485416005710533 (2 : ZMod 485416005710533)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (100375518137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (100375518137, 1)] : List FactorBlock).map factorBlockValue).prod) = 485416005710533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_100375518137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 485416005710533) ^ 242708002855266 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 485416005710533) ^ 161805335236844 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 485416005710533) ^ 37339692746964 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 485416005710533) ^ 15658580829372 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 485416005710533) ^ 4836 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_576241538698151 : Nat.Prime 576241538698151 := by
  apply lucas_primality 576241538698151 (7 : ZMod 576241538698151)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (401519, 1), (2207929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (401519, 1), (2207929, 1)] : List FactorBlock).map factorBlockValue).prod) = 576241538698151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_401519
      · exact prime_fortySevenAS_2207929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 576241538698151) ^ 288120769349075 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 576241538698151) ^ 115248307739630 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 576241538698151) ^ 44326272207550 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 576241538698151) ^ 1435153850 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 576241538698151) ^ 260987350 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_600507531266689 : Nat.Prime 600507531266689 := by
  apply lucas_primality 600507531266689 (11 : ZMod 600507531266689)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (19, 1), (9145156117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (19, 1), (9145156117, 1)] : List FactorBlock).map factorBlockValue).prod) = 600507531266689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_9145156117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 600507531266689) ^ 300253765633344 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 600507531266689) ^ 200169177088896 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 600507531266689) ^ 31605659540352 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (11 : ZMod 600507531266689) ^ 65664 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_691177233576727 : Nat.Prime 691177233576727 := by
  apply lucas_primality 691177233576727 (3 : ZMod 691177233576727)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (984582953813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (984582953813, 1)] : List FactorBlock).map factorBlockValue).prod) = 691177233576727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_984582953813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 691177233576727) ^ 345588616788363 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 691177233576727) ^ 230392411192242 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 691177233576727) ^ 53167479505902 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 691177233576727) ^ 702 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_894101403975449 : Nat.Prime 894101403975449 := by
  apply lucas_primality 894101403975449 (3 : ZMod 894101403975449)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3727, 1), (29987302253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3727, 1), (29987302253, 1)] : List FactorBlock).map factorBlockValue).prod) = 894101403975449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3727
      · exact prime_fortySevenAS_29987302253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 894101403975449) ^ 447050701987724 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 894101403975449) ^ 239898418024 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 894101403975449) ^ 29816 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_941171938028653 : Nat.Prime 941171938028653 := by
  apply lucas_primality 941171938028653 (2 : ZMod 941171938028653)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (23, 1), (167, 1), (109194763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (23, 1), (167, 1), (109194763, 1)] : List FactorBlock).map factorBlockValue).prod) = 941171938028653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_167
      · exact prime_fortySevenAS_109194763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 941171938028653) ^ 470585969014326 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 313723979342884 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 85561085275332 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 55363055178156 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 40920519044724 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 5635760107956 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 941171938028653) ^ 8619204 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1079635724448163 : Nat.Prime 1079635724448163 := by
  apply lucas_primality 1079635724448163 (2 : ZMod 1079635724448163)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12527, 1), (2052016643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12527, 1), (2052016643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079635724448163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_12527
      · exact prime_fortySevenAS_2052016643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1079635724448163) ^ 539817862224081 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1079635724448163) ^ 359878574816054 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1079635724448163) ^ 154233674921166 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1079635724448163) ^ 86184699006 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1079635724448163) ^ 526134 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1901073293018377 : Nat.Prime 1901073293018377 := by
  apply lucas_primality 1901073293018377 (10 : ZMod 1901073293018377)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (467, 1), (169617531497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (467, 1), (169617531497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1901073293018377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_467
      · exact prime_fortySevenAS_169617531497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1901073293018377) ^ 950536646509188 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1901073293018377) ^ 633691097672792 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1901073293018377) ^ 4070820755928 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 1901073293018377) ^ 11208 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1944324797139467 : Nat.Prime 1944324797139467 := by
  apply lucas_primality 1944324797139467 (2 : ZMod 1944324797139467)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5099, 1), (100537, 1), (270913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5099, 1), (100537, 1), (270913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1944324797139467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_5099
      · exact prime_fortySevenAS_100537
      · exact prime_fortySevenAS_270913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1944324797139467) ^ 972162398569733 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944324797139467) ^ 277760685305638 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944324797139467) ^ 381314923934 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944324797139467) ^ 19339395418 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944324797139467) ^ 7176934282 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5227634314962817 : Nat.Prime 5227634314962817 := by
  apply lucas_primality 5227634314962817 (15 : ZMod 5227634314962817)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (3049, 1), (3433, 1), (1300597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (3049, 1), (3433, 1), (1300597, 1)] : List FactorBlock).map factorBlockValue).prod) = 5227634314962817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_3049
      · exact prime_fortySevenAS_3433
      · exact prime_fortySevenAS_1300597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 5227634314962817) ^ 2613817157481408 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (15 : ZMod 5227634314962817) ^ 1742544771654272 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (15 : ZMod 5227634314962817) ^ 1714540608384 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (15 : ZMod 5227634314962817) ^ 1522759777152 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (15 : ZMod 5227634314962817) ^ 4019411328 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5924482459677647 : Nat.Prime 5924482459677647 := by
  apply lucas_primality 5924482459677647 (5 : ZMod 5924482459677647)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (42499, 1), (2403497713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (42499, 1), (2403497713, 1)] : List FactorBlock).map factorBlockValue).prod) = 5924482459677647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_42499
      · exact prime_fortySevenAS_2403497713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5924482459677647) ^ 2962241229838823 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 5924482459677647) ^ 204292498609574 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 5924482459677647) ^ 139402867354 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 5924482459677647) ^ 2464942 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_6781740207771077 : Nat.Prime 6781740207771077 := by
  apply lucas_primality 6781740207771077 (2 : ZMod 6781740207771077)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (1495853, 1), (5872661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (1495853, 1), (5872661, 1)] : List FactorBlock).map factorBlockValue).prod) = 6781740207771077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_193
      · exact prime_fortySevenAS_1495853
      · exact prime_fortySevenAS_5872661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6781740207771077) ^ 3390870103885538 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6781740207771077) ^ 35138550299332 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6781740207771077) ^ 4533694292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 6781740207771077) ^ 1154798516 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_7228777727467847 : Nat.Prime 7228777727467847 := by
  apply lucas_primality 7228777727467847 (5 : ZMod 7228777727467847)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (211, 1), (1557255003763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (211, 1), (1557255003763, 1)] : List FactorBlock).map factorBlockValue).prod) = 7228777727467847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_211
      · exact prime_fortySevenAS_1557255003763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7228777727467847) ^ 3614388863733923 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 7228777727467847) ^ 657161611587986 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 7228777727467847) ^ 34259610082786 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 7228777727467847) ^ 4642 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_8440965764992513 : Nat.Prime 8440965764992513 := by
  apply lucas_primality 8440965764992513 (10 : ZMod 8440965764992513)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (17, 1), (89, 1), (269, 1), (4500787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (17, 1), (89, 1), (269, 1), (4500787, 1)] : List FactorBlock).map factorBlockValue).prod) = 8440965764992513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_89
      · exact prime_fortySevenAS_269
      · exact prime_fortySevenAS_4500787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8440965764992513) ^ 4220482882496256 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 8440965764992513) ^ 2813655254997504 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 8440965764992513) ^ 496527397940736 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 8440965764992513) ^ 94842311966208 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 8440965764992513) ^ 31379054888448 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 8440965764992513) ^ 1875442176 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_9443702141938769 : Nat.Prime 9443702141938769 := by
  apply lucas_primality 9443702141938769 (3 : ZMod 9443702141938769)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (1709, 1), (14149, 1), (2219023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (1709, 1), (14149, 1), (2219023, 1)] : List FactorBlock).map factorBlockValue).prod) = 9443702141938769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_1709
      · exact prime_fortySevenAS_14149
      · exact prime_fortySevenAS_2219023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9443702141938769) ^ 4721851070969384 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 9443702141938769) ^ 858518376539888 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 9443702141938769) ^ 5525864331152 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 9443702141938769) ^ 667446614032 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 9443702141938769) ^ 4255792816 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_21953851986468161 : Nat.Prime 21953851986468161 := by
  apply lucas_primality 21953851986468161 (13 : ZMod 21953851986468161)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 1), (19, 1), (677, 1), (1609, 1), (301349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 1), (19, 1), (677, 1), (1609, 1), (301349, 1)] : List FactorBlock).map factorBlockValue).prod) = 21953851986468161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_677
      · exact prime_fortySevenAS_1609
      · exact prime_fortySevenAS_301349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 21953851986468161) ^ 10976925993234080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 4390770397293632 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 1995804726042560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 1155465894024640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 32428141782080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 13644407698240 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 21953851986468161) ^ 72851915840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_24086475195090479 : Nat.Prime 24086475195090479 := by
  apply lucas_primality 24086475195090479 (13 : ZMod 24086475195090479)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (124157088634487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (124157088634487, 1)] : List FactorBlock).map factorBlockValue).prod) = 24086475195090479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_97
      · exact prime_fortySevenAS_124157088634487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 24086475195090479) ^ 12043237597545239 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24086475195090479) ^ 248314177268974 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24086475195090479) ^ 194 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_24293949631261601 : Nat.Prime 24293949631261601 := by
  apply lucas_primality 24293949631261601 (3 : ZMod 24293949631261601)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (30367437039077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (30367437039077, 1)] : List FactorBlock).map factorBlockValue).prod) = 24293949631261601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_30367437039077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24293949631261601) ^ 12146974815630800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 24293949631261601) ^ 4858789926252320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 24293949631261601) ^ 800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_24748757490892177 : Nat.Prime 24748757490892177 := by
  apply lucas_primality 24748757490892177 (13 : ZMod 24748757490892177)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (17, 1), (365231, 1), (3954361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (17, 1), (365231, 1), (3954361, 1)] : List FactorBlock).map factorBlockValue).prod) = 24748757490892177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_365231
      · exact prime_fortySevenAS_3954361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24748757490892177) ^ 12374378745446088 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24748757490892177) ^ 8249585830297392 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24748757490892177) ^ 3535536784413168 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24748757490892177) ^ 1455809264170128 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24748757490892177) ^ 67761930096 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 24748757490892177) ^ 6258598416 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_31805116698921113 : Nat.Prime 31805116698921113 := by
  apply lucas_primality 31805116698921113 (3 : ZMod 31805116698921113)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (825613, 1), (4815379103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (825613, 1), (4815379103, 1)] : List FactorBlock).map factorBlockValue).prod) = 31805116698921113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_825613
      · exact prime_fortySevenAS_4815379103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31805116698921113) ^ 15902558349460556 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 31805116698921113) ^ 38523032824 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 31805116698921113) ^ 6604904 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_37058457600931373 : Nat.Prime 37058457600931373 := by
  apply lucas_primality 37058457600931373 (2 : ZMod 37058457600931373)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (28260697, 1), (327826819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (28260697, 1), (327826819, 1)] : List FactorBlock).map factorBlockValue).prod) = 37058457600931373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_28260697
      · exact prime_fortySevenAS_327826819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37058457600931373) ^ 18529228800465686 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 37058457600931373) ^ 1311307276 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 37058457600931373) ^ 113042788 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_65575138255055761 : Nat.Prime 65575138255055761 := by
  apply lucas_primality 65575138255055761 (7 : ZMod 65575138255055761)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23, 1), (29, 1), (123083, 1), (3328159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23, 1), (29, 1), (123083, 1), (3328159, 1)] : List FactorBlock).map factorBlockValue).prod) = 65575138255055761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_123083
      · exact prime_fortySevenAS_3328159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 65575138255055761) ^ 32787569127527880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 21858379418351920 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 13115027651011152 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 2851092967611120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 2261211663967440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 532771692720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 65575138255055761) ^ 19703126640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_69377933255426251 : Nat.Prime 69377933255426251 := by
  apply lucas_primality 69377933255426251 (3 : ZMod 69377933255426251)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (7, 4), (13, 1), (592726819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (7, 4), (13, 1), (592726819, 1)] : List FactorBlock).map factorBlockValue).prod) = 69377933255426251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_592726819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69377933255426251) ^ 34688966627713125 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 69377933255426251) ^ 23125977751808750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 69377933255426251) ^ 13875586651085250 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 69377933255426251) ^ 9911133322203750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 69377933255426251) ^ 5336764096571250 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 69377933255426251) ^ 117048750 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_214655483703109979 : Nat.Prime 214655483703109979 := by
  apply lucas_primality 214655483703109979 (2 : ZMod 214655483703109979)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (3571, 1), (179972301577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (3571, 1), (179972301577, 1)] : List FactorBlock).map factorBlockValue).prod) = 214655483703109979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_167
      · exact prime_fortySevenAS_3571
      · exact prime_fortySevenAS_179972301577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 214655483703109979) ^ 107327741851554989 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 214655483703109979) ^ 1285362177862934 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 214655483703109979) ^ 60110748726718 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 214655483703109979) ^ 1192714 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_258408660915376369 : Nat.Prime 258408660915376369 := by
  apply lucas_primality 258408660915376369 (7 : ZMod 258408660915376369)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (151, 1), (601, 1), (59321812091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (151, 1), (601, 1), (59321812091, 1)] : List FactorBlock).map factorBlockValue).prod) = 258408660915376369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_151
      · exact prime_fortySevenAS_601
      · exact prime_fortySevenAS_59321812091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 258408660915376369) ^ 129204330457688184 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 258408660915376369) ^ 86136220305125456 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 258408660915376369) ^ 1711315635201168 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 258408660915376369) ^ 429964494035568 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 258408660915376369) ^ 4356048 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_276386745458729729 : Nat.Prime 276386745458729729 := by
  apply lucas_primality 276386745458729729 (3 : ZMod 276386745458729729)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (1079635724448163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (1079635724448163, 1)] : List FactorBlock).map factorBlockValue).prod) = 276386745458729729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_1079635724448163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 276386745458729729) ^ 138193372729364864 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 276386745458729729) ^ 256 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_287453394624700921 : Nat.Prime 287453394624700921 := by
  apply lucas_primality 287453394624700921 (13 : ZMod 287453394624700921)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (4692173, 1), (6630121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (4692173, 1), (6630121, 1)] : List FactorBlock).map factorBlockValue).prod) = 287453394624700921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_4692173
      · exact prime_fortySevenAS_6630121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 287453394624700921) ^ 143726697312350460 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 95817798208233640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 57490678924940184 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 41064770660671560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 26132126784063720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 61262318040 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (13 : ZMod 287453394624700921) ^ 43355678520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_291679132971846877 : Nat.Prime 291679132971846877 := by
  apply lucas_primality 291679132971846877 (2 : ZMod 291679132971846877)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1213, 1), (20038412542721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1213, 1), (20038412542721, 1)] : List FactorBlock).map factorBlockValue).prod) = 291679132971846877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_1213
      · exact prime_fortySevenAS_20038412542721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 291679132971846877) ^ 145839566485923438 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 291679132971846877) ^ 97226377657282292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 291679132971846877) ^ 240460950512652 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 291679132971846877) ^ 14556 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_346559089736443487 : Nat.Prime 346559089736443487 := by
  apply lucas_primality 346559089736443487 (19 : ZMod 346559089736443487)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13936387, 1), (253747061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13936387, 1), (253747061, 1)] : List FactorBlock).map factorBlockValue).prod) = 346559089736443487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_13936387
      · exact prime_fortySevenAS_253747061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 346559089736443487) ^ 173279544868221743 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 346559089736443487) ^ 49508441390920498 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 346559089736443487) ^ 24867211978 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 346559089736443487) ^ 1365765926 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_383441090072900243 : Nat.Prime 383441090072900243 := by
  apply lucas_primality 383441090072900243 (2 : ZMod 383441090072900243)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (117617, 1), (1630041108313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (117617, 1), (1630041108313, 1)] : List FactorBlock).map factorBlockValue).prod) = 383441090072900243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_117617
      · exact prime_fortySevenAS_1630041108313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 383441090072900243) ^ 191720545036450121 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 383441090072900243) ^ 3260082216626 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 383441090072900243) ^ 235234 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_463642025950027871 : Nat.Prime 463642025950027871 := by
  apply lucas_primality 463642025950027871 (7 : ZMod 463642025950027871)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (34369, 1), (208213037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (34369, 1), (208213037, 1)] : List FactorBlock).map factorBlockValue).prod) = 463642025950027871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_34369
      · exact prime_fortySevenAS_208213037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 463642025950027871) ^ 231821012975013935 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 92728405190005574 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 42149275086366170 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 24402211892106730 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 14956194385484770 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 13490122667230 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 463642025950027871) ^ 2226767510 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_61717
      · exact prime_fortySevenAS_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_594056865485916901 : Nat.Prime 594056865485916901 := by
  apply lucas_primality 594056865485916901 (2 : ZMod 594056865485916901)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (17444461, 1), (37837981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (17444461, 1), (37837981, 1)] : List FactorBlock).map factorBlockValue).prod) = 594056865485916901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_17444461
      · exact prime_fortySevenAS_37837981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 594056865485916901) ^ 297028432742958450 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 594056865485916901) ^ 198018955161972300 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 594056865485916901) ^ 118811373097183380 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 594056865485916901) ^ 34054182900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 594056865485916901) ^ 15700014900 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_776976306864094027 : Nat.Prime 776976306864094027 := by
  apply lucas_primality 776976306864094027 (2 : ZMod 776976306864094027)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6029, 1), (108301, 1), (66108533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6029, 1), (108301, 1), (66108533, 1)] : List FactorBlock).map factorBlockValue).prod) = 776976306864094027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_6029
      · exact prime_fortySevenAS_108301
      · exact prime_fortySevenAS_66108533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 776976306864094027) ^ 388488153432047013 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 776976306864094027) ^ 258992102288031342 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 776976306864094027) ^ 128873164183794 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 776976306864094027) ^ 7174230218226 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 776976306864094027) ^ 11753041122 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1343234302814898521 : Nat.Prime 1343234302814898521 := by
  apply lucas_primality 1343234302814898521 (3 : ZMod 1343234302814898521)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (463, 1), (158537, 1), (35191421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (463, 1), (158537, 1), (35191421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343234302814898521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_463
      · exact prime_fortySevenAS_158537
      · exact prime_fortySevenAS_35191421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1343234302814898521) ^ 671617151407449260 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343234302814898521) ^ 268646860562979704 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343234302814898521) ^ 103325715601146040 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343234302814898521) ^ 2901154001760040 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343234302814898521) ^ 8472686519960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343234302814898521) ^ 38169368120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1619809019274659107 : Nat.Prime 1619809019274659107 := by
  apply lucas_primality 1619809019274659107 (3 : ZMod 1619809019274659107)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29723, 1), (37223, 1), (10609153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29723, 1), (37223, 1), (10609153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1619809019274659107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29723
      · exact prime_fortySevenAS_37223
      · exact prime_fortySevenAS_10609153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1619809019274659107) ^ 809904509637329553 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619809019274659107) ^ 539936339758219702 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619809019274659107) ^ 70426479098898222 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619809019274659107) ^ 54496821292422 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619809019274659107) ^ 43516347937422 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 1619809019274659107) ^ 152680333602 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1699805095970705953 : Nat.Prime 1699805095970705953 := by
  apply lucas_primality 1699805095970705953 (5 : ZMod 1699805095970705953)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (176329, 1), (100416284803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (176329, 1), (100416284803, 1)] : List FactorBlock).map factorBlockValue).prod) = 1699805095970705953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_176329
      · exact prime_fortySevenAS_100416284803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1699805095970705953) ^ 849902547985352976 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699805095970705953) ^ 566601698656901984 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699805095970705953) ^ 9639963341088 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 1699805095970705953) ^ 16927584 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1756789875970627213 : Nat.Prime 1756789875970627213 := by
  apply lucas_primality 1756789875970627213 (6 : ZMod 1756789875970627213)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (13, 1), (101, 1), (4517, 1), (68001287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (13, 1), (101, 1), (4517, 1), (68001287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1756789875970627213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_101
      · exact prime_fortySevenAS_4517
      · exact prime_fortySevenAS_68001287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1756789875970627213) ^ 878394937985313606 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 585596625323542404 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 159708170542784292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 135137682766971324 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 17393959168026012 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 388928464903836 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (6 : ZMod 1756789875970627213) ^ 25834656276 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2189862548474625487 : Nat.Prime 2189862548474625487 := by
  apply lucas_primality 2189862548474625487 (3 : ZMod 2189862548474625487)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (11, 1), (43, 1), (113, 1), (11047, 1), (1090181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (11, 1), (43, 1), (113, 1), (11047, 1), (1090181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2189862548474625487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_113
      · exact prime_fortySevenAS_11047
      · exact prime_fortySevenAS_1090181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2189862548474625487) ^ 1094931274237312743 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 729954182824875162 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 312837506924946498 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 199078413497693226 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 50927036011037802 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 19379314588271022 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 198231424683138 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2189862548474625487) ^ 2008714652406 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2668208947267058857 : Nat.Prime 2668208947267058857 := by
  apply lucas_primality 2668208947267058857 (10 : ZMod 2668208947267058857)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37058457600931373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37058457600931373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2668208947267058857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_37058457600931373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2668208947267058857) ^ 1334104473633529428 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 2668208947267058857) ^ 889402982422352952 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 2668208947267058857) ^ 72 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5563704311400334453 : Nat.Prime 5563704311400334453 := by
  apply lucas_primality 5563704311400334453 (2 : ZMod 5563704311400334453)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463642025950027871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463642025950027871, 1)] : List FactorBlock).map factorBlockValue).prod) = 5563704311400334453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_463642025950027871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5563704311400334453) ^ 2781852155700167226 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5563704311400334453) ^ 1854568103800111484 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5563704311400334453) ^ 12 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_8465719750144016849 : Nat.Prime 8465719750144016849 := by
  apply lucas_primality 8465719750144016849 (3 : ZMod 8465719750144016849)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (53, 1), (116849, 1), (2083815089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (53, 1), (116849, 1), (2083815089, 1)] : List FactorBlock).map factorBlockValue).prod) = 8465719750144016849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_116849
      · exact prime_fortySevenAS_2083815089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8465719750144016849) ^ 4232859875072008424 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 8465719750144016849) ^ 206480969515707728 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 8465719750144016849) ^ 159730561323472016 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 8465719750144016849) ^ 72450083014352 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 8465719750144016849) ^ 4062606032 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_8489509759485751153 : Nat.Prime 8489509759485751153 := by
  apply lucas_primality 8489509759485751153 (7 : ZMod 8489509759485751153)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (19, 1), (102769, 1), (6967585243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (19, 1), (102769, 1), (6967585243, 1)] : List FactorBlock).map factorBlockValue).prod) = 8489509759485751153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_102769
      · exact prime_fortySevenAS_6967585243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8489509759485751153) ^ 4244754879742875576 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 8489509759485751153) ^ 2829836586495250384 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 8489509759485751153) ^ 653039212268134704 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 8489509759485751153) ^ 446816303130829008 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 8489509759485751153) ^ 82607690641008 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 8489509759485751153) ^ 1218429264 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_22177421247579552907 : Nat.Prime 22177421247579552907 := by
  apply lucas_primality 22177421247579552907 (2 : ZMod 22177421247579552907)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (4021, 1), (33479, 1), (49651013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (4021, 1), (33479, 1), (49651013, 1)] : List FactorBlock).map factorBlockValue).prod) = 22177421247579552907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_79
      · exact prime_fortySevenAS_4021
      · exact prime_fortySevenAS_33479
      · exact prime_fortySevenAS_49651013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22177421247579552907) ^ 11088710623789776453 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 7392473749193184302 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 3168203035368507558 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 280726851235184214 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 5515399464705186 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 662427827819814 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 22177421247579552907) ^ 446666037762 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_107173532234745964573 : Nat.Prime 107173532234745964573 := by
  apply lucas_primality 107173532234745964573 (5 : ZMod 107173532234745964573)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (54069161, 1), (12706130617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (54069161, 1), (12706130617, 1)] : List FactorBlock).map factorBlockValue).prod) = 107173532234745964573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_54069161
      · exact prime_fortySevenAS_12706130617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 107173532234745964573) ^ 53586766117372982286 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 107173532234745964573) ^ 35724510744915321524 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 107173532234745964573) ^ 8244117864211228044 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 107173532234745964573) ^ 1982156376252 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 107173532234745964573) ^ 8434789116 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_164404641816758219563 : Nat.Prime 164404641816758219563 := by
  apply lucas_primality 164404641816758219563 (2 : ZMod 164404641816758219563)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (131, 1), (62687, 1), (52963111757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (131, 1), (62687, 1), (52963111757, 1)] : List FactorBlock).map factorBlockValue).prod) = 164404641816758219563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_131
      · exact prime_fortySevenAS_62687
      · exact prime_fortySevenAS_52963111757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 164404641816758219563) ^ 82202320908379109781 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 164404641816758219563) ^ 54801547272252739854 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 164404641816758219563) ^ 23486377402394031366 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 164404641816758219563) ^ 1254997265776780302 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 164404641816758219563) ^ 2622627367983126 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 164404641816758219563) ^ 3104134866 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_285631826227671508771 : Nat.Prime 285631826227671508771 := by
  apply lucas_primality 285631826227671508771 (2 : ZMod 285631826227671508771)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (839, 1), (2551, 1), (4448493112031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (839, 1), (2551, 1), (4448493112031, 1)] : List FactorBlock).map factorBlockValue).prod) = 285631826227671508771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_839
      · exact prime_fortySevenAS_2551
      · exact prime_fortySevenAS_4448493112031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 285631826227671508771) ^ 142815913113835754385 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 285631826227671508771) ^ 95210608742557169590 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 285631826227671508771) ^ 57126365245534301754 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 285631826227671508771) ^ 340443177863732430 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 285631826227671508771) ^ 111968571629820270 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 285631826227671508771) ^ 64208670 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_298273596753408237817 : Nat.Prime 298273596753408237817 := by
  apply lucas_primality 298273596753408237817 (5 : ZMod 298273596753408237817)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (720127, 1), (17258159368267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (720127, 1), (17258159368267, 1)] : List FactorBlock).map factorBlockValue).prod) = 298273596753408237817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_720127
      · exact prime_fortySevenAS_17258159368267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 298273596753408237817) ^ 149136798376704118908 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 298273596753408237817) ^ 99424532251136079272 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 298273596753408237817) ^ 414195824838408 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 298273596753408237817) ^ 17283048 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_302804748289231467329 : Nat.Prime 302804748289231467329 := by
  apply lucas_primality 302804748289231467329 (3 : ZMod 302804748289231467329)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (137, 1), (899881, 1), (5482504763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (137, 1), (899881, 1), (5482504763, 1)] : List FactorBlock).map factorBlockValue).prod) = 302804748289231467329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_137
      · exact prime_fortySevenAS_899881
      · exact prime_fortySevenAS_5482504763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 302804748289231467329) ^ 151402374144615733664 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 302804748289231467329) ^ 43257821184175923904 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 302804748289231467329) ^ 2210253637147674944 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 302804748289231467329) ^ 336494212333888 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 302804748289231467329) ^ 55231096256 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_631981455880965713323 : Nat.Prime 631981455880965713323 := by
  apply lucas_primality 631981455880965713323 (2 : ZMod 631981455880965713323)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (105361, 1), (3430331, 1), (291431957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (105361, 1), (3430331, 1), (291431957, 1)] : List FactorBlock).map factorBlockValue).prod) = 631981455880965713323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_105361
      · exact prime_fortySevenAS_3430331
      · exact prime_fortySevenAS_291431957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 631981455880965713323) ^ 315990727940482856661 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 631981455880965713323) ^ 210660485293655237774 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 631981455880965713323) ^ 5998248458926602 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 631981455880965713323) ^ 184233374528862 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 631981455880965713323) ^ 2168538626946 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_633614756815087963423 : Nat.Prime 633614756815087963423 := by
  apply lucas_primality 633614756815087963423 (3 : ZMod 633614756815087963423)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (293, 1), (1301, 1), (11801, 1), (1805788793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (293, 1), (1301, 1), (11801, 1), (1805788793, 1)] : List FactorBlock).map factorBlockValue).prod) = 633614756815087963423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_293
      · exact prime_fortySevenAS_1301
      · exact prime_fortySevenAS_11801
      · exact prime_fortySevenAS_1805788793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 633614756815087963423) ^ 316807378407543981711 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 211204918938362654474 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 48739596678083689494 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 2162507702440573254 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 487021334984694822 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 53691615694863822 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 633614756815087963423) ^ 350879770254 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_779334335168194956461 : Nat.Prime 779334335168194956461 := by
  apply lucas_primality 779334335168194956461 (2 : ZMod 779334335168194956461)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (107273, 1), (12525797621219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (107273, 1), (12525797621219, 1)] : List FactorBlock).map factorBlockValue).prod) = 779334335168194956461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_107273
      · exact prime_fortySevenAS_12525797621219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 779334335168194956461) ^ 389667167584097478230 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 779334335168194956461) ^ 155866867033638991292 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 779334335168194956461) ^ 26873597764420515740 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 779334335168194956461) ^ 7264962620307020 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 779334335168194956461) ^ 62218340 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1246795977111482196803 : Nat.Prime 1246795977111482196803 := by
  apply lucas_primality 1246795977111482196803 (2 : ZMod 1246795977111482196803)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1291, 1), (12473, 1), (46681, 1), (63794719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1291, 1), (12473, 1), (46681, 1), (63794719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1246795977111482196803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_1291
      · exact prime_fortySevenAS_12473
      · exact prime_fortySevenAS_46681
      · exact prime_fortySevenAS_63794719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1246795977111482196803) ^ 623397988555741098401 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246795977111482196803) ^ 95907382854729399754 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246795977111482196803) ^ 965759858335772422 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246795977111482196803) ^ 99959590885230674 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246795977111482196803) ^ 26708853218900242 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246795977111482196803) ^ 19543874424958 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2186149460832290840921 : Nat.Prime 2186149460832290840921 := by
  apply lucas_primality 2186149460832290840921 (3 : ZMod 2186149460832290840921)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (5557, 1), (894101403975449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (5557, 1), (894101403975449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2186149460832290840921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_5557
      · exact prime_fortySevenAS_894101403975449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2186149460832290840921) ^ 1093074730416145420460 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2186149460832290840921) ^ 437229892166458168184 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2186149460832290840921) ^ 198740860075662803720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2186149460832290840921) ^ 393404617749197560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 2186149460832290840921) ^ 2445080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_107
      · exact prime_fortySevenAS_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2771761843949960255293 : Nat.Prime 2771761843949960255293 := by
  apply lucas_primality 2771761843949960255293 (2 : ZMod 2771761843949960255293)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (17, 1), (61, 1), (24748757490892177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (17, 1), (61, 1), (24748757490892177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2771761843949960255293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_61
      · exact prime_fortySevenAS_24748757490892177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2771761843949960255293) ^ 1385880921974980127646 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771761843949960255293) ^ 923920614649986751764 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771761843949960255293) ^ 163044814349997662076 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771761843949960255293) ^ 45438718753278036972 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 2771761843949960255293) ^ 111996 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5327979091087515805199 : Nat.Prime 5327979091087515805199 := by
  apply lucas_primality 5327979091087515805199 (19 : ZMod 5327979091087515805199)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (101, 1), (44497, 1), (624643, 1), (946123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (101, 1), (44497, 1), (624643, 1), (946123, 1)] : List FactorBlock).map factorBlockValue).prod) = 5327979091087515805199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_101
      · exact prime_fortySevenAS_44497
      · exact prime_fortySevenAS_624643
      · exact prime_fortySevenAS_946123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 5327979091087515805199) ^ 2663989545543757902599 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 313410534769853870894 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 90304730357415522122 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 52752268228589265398 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 119737939436085934 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 8529638675351386 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (19 : ZMod 5327979091087515805199) ^ 5631381005522026 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_18404667383036858516053 : Nat.Prime 18404667383036858516053 := by
  apply lucas_primality 18404667383036858516053 (2 : ZMod 18404667383036858516053)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1992533, 1), (256578315460729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1992533, 1), (256578315460729, 1)] : List FactorBlock).map factorBlockValue).prod) = 18404667383036858516053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_1992533
      · exact prime_fortySevenAS_256578315460729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18404667383036858516053) ^ 9202333691518429258026 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18404667383036858516053) ^ 6134889127678952838684 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18404667383036858516053) ^ 9236819356586244 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18404667383036858516053) ^ 71731188 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_26252129452182504786119 : Nat.Prime 26252129452182504786119 := by
  apply lucas_primality 26252129452182504786119 (7 : ZMod 26252129452182504786119)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (222149, 1), (8440965764992513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (222149, 1), (8440965764992513, 1)] : List FactorBlock).map factorBlockValue).prod) = 26252129452182504786119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_222149
      · exact prime_fortySevenAS_8440965764992513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 26252129452182504786119) ^ 13126064726091252393059 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 26252129452182504786119) ^ 3750304207454643540874 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 26252129452182504786119) ^ 118173520709895182 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 26252129452182504786119) ^ 3110086 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_43405936408599430206407 : Nat.Prime 43405936408599430206407 := by
  apply lucas_primality 43405936408599430206407 (5 : ZMod 43405936408599430206407)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83987, 1), (258408660915376369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83987, 1), (258408660915376369, 1)] : List FactorBlock).map factorBlockValue).prod) = 43405936408599430206407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_83987
      · exact prime_fortySevenAS_258408660915376369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 43405936408599430206407) ^ 21702968204299715103203 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 43405936408599430206407) ^ 516817321830752738 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 43405936408599430206407) ^ 167974 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_68076648946483116471401 : Nat.Prime 68076648946483116471401 := by
  apply lucas_primality 68076648946483116471401 (3 : ZMod 68076648946483116471401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (53, 1), (114044191, 1), (5119487069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (53, 1), (114044191, 1), (5119487069, 1)] : List FactorBlock).map factorBlockValue).prod) = 68076648946483116471401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_114044191
      · exact prime_fortySevenAS_5119487069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68076648946483116471401) ^ 34038324473241558235700 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 68076648946483116471401) ^ 13615329789296623294280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 68076648946483116471401) ^ 6188786267862101497400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 68076648946483116471401) ^ 1284465074461945593800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 68076648946483116471401) ^ 596932192245400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 68076648946483116471401) ^ 13297552670600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_95221890149281030134683 : Nat.Prime 95221890149281030134683 := by
  apply lucas_primality 95221890149281030134683 (2 : ZMod 95221890149281030134683)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (216649, 1), (330703, 1), (28892434861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (216649, 1), (330703, 1), (28892434861, 1)] : List FactorBlock).map factorBlockValue).prod) = 95221890149281030134683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_216649
      · exact prime_fortySevenAS_330703
      · exact prime_fortySevenAS_28892434861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95221890149281030134683) ^ 47610945074640515067341 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 95221890149281030134683) ^ 4140082180403523049334 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 95221890149281030134683) ^ 439521484748515018 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 95221890149281030134683) ^ 287937787529236294 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 95221890149281030134683) ^ 3295737815362 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1660983546147923912627309 : Nat.Prime 1660983546147923912627309 := by
  apply lucas_primality 1660983546147923912627309 (2 : ZMod 1660983546147923912627309)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2531, 1), (837305507, 1), (195942771331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2531, 1), (837305507, 1), (195942771331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1660983546147923912627309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_2531
      · exact prime_fortySevenAS_837305507
      · exact prime_fortySevenAS_195942771331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1660983546147923912627309) ^ 830491773073961956313654 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1660983546147923912627309) ^ 656255845969152079268 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1660983546147923912627309) ^ 1983724616955044 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 1660983546147923912627309) ^ 8476880952868 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5039592195976115234267549 : Nat.Prime 5039592195976115234267549 := by
  apply lucas_primality 5039592195976115234267549 (2 : ZMod 5039592195976115234267549)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11172970381, 1), (112763034898627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11172970381, 1), (112763034898627, 1)] : List FactorBlock).map factorBlockValue).prod) = 5039592195976115234267549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11172970381
      · exact prime_fortySevenAS_112763034898627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5039592195976115234267549) ^ 2519796097988057617133774 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5039592195976115234267549) ^ 451052139594508 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5039592195976115234267549) ^ 44691881524 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5469147987483528206007283 : Nat.Prime 5469147987483528206007283 := by
  apply lucas_primality 5469147987483528206007283 (2 : ZMod 5469147987483528206007283)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (43405936408599430206407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (43405936408599430206407, 1)] : List FactorBlock).map factorBlockValue).prod) = 5469147987483528206007283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_43405936408599430206407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5469147987483528206007283) ^ 2734573993741764103003641 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5469147987483528206007283) ^ 1823049329161176068669094 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5469147987483528206007283) ^ 781306855354789743715326 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 5469147987483528206007283) ^ 126 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_7570373781039870105317983 : Nat.Prime 7570373781039870105317983 := by
  apply lucas_primality 7570373781039870105317983 (3 : ZMod 7570373781039870105317983)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (3956681, 1), (5227634314962817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (3956681, 1), (5227634314962817, 1)] : List FactorBlock).map factorBlockValue).prod) = 7570373781039870105317983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_61
      · exact prime_fortySevenAS_3956681
      · exact prime_fortySevenAS_5227634314962817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7570373781039870105317983) ^ 3785186890519935052658991 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 7570373781039870105317983) ^ 2523457927013290035105994 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 7570373781039870105317983) ^ 124104488213768362382262 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 7570373781039870105317983) ^ 1913314159276391022 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 7570373781039870105317983) ^ 1448145246 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_8335815114436340620017101 : Nat.Prime 8335815114436340620017101 := by
  apply lucas_primality 8335815114436340620017101 (2 : ZMod 8335815114436340620017101)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13938361, 1), (31717381, 1), (188555431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13938361, 1), (31717381, 1), (188555431, 1)] : List FactorBlock).map factorBlockValue).prod) = 8335815114436340620017101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_13938361
      · exact prime_fortySevenAS_31717381
      · exact prime_fortySevenAS_188555431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8335815114436340620017101) ^ 4167907557218170310008550 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 8335815114436340620017101) ^ 1667163022887268124003420 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 8335815114436340620017101) ^ 598048444464621100 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 8335815114436340620017101) ^ 262815366578859100 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 8335815114436340620017101) ^ 44208830635254100 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_10572021223902710535204337 : Nat.Prime 10572021223902710535204337 := by
  apply lucas_primality 10572021223902710535204337 (5 : ZMod 10572021223902710535204337)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (8369, 1), (1605714247, 1), (16389849299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (8369, 1), (1605714247, 1), (16389849299, 1)] : List FactorBlock).map factorBlockValue).prod) = 10572021223902710535204337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_8369
      · exact prime_fortySevenAS_1605714247
      · exact prime_fortySevenAS_16389849299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10572021223902710535204337) ^ 5286010611951355267602168 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572021223902710535204337) ^ 3524007074634236845068112 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572021223902710535204337) ^ 1263235897228188616944 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572021223902710535204337) ^ 6583999141599888 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (5 : ZMod 10572021223902710535204337) ^ 645034681590864 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_10582087898082774056948009 : Nat.Prime 10582087898082774056948009 := by
  apply lucas_primality 10582087898082774056948009 (3 : ZMod 10582087898082774056948009)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (421, 1), (285631826227671508771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (421, 1), (285631826227671508771, 1)] : List FactorBlock).map factorBlockValue).prod) = 10582087898082774056948009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_421
      · exact prime_fortySevenAS_285631826227671508771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10582087898082774056948009) ^ 5291043949041387028474004 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 10582087898082774056948009) ^ 962007990734797641540728 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 10582087898082774056948009) ^ 25135600708035092771848 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 10582087898082774056948009) ^ 37048 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_17792681252908308220632083 : Nat.Prime 17792681252908308220632083 := by
  apply lucas_primality 17792681252908308220632083 (2 : ZMod 17792681252908308220632083)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (98523674329, 1), (90296476324529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (98523674329, 1), (90296476324529, 1)] : List FactorBlock).map factorBlockValue).prod) = 17792681252908308220632083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_98523674329
      · exact prime_fortySevenAS_90296476324529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17792681252908308220632083) ^ 8896340626454154110316041 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 17792681252908308220632083) ^ 180592952649058 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 17792681252908308220632083) ^ 197047348658 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_18848895370703068715411803 : Nat.Prime 18848895370703068715411803 := by
  apply lucas_primality 18848895370703068715411803 (2 : ZMod 18848895370703068715411803)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (45280717, 1), (69377933255426251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (45280717, 1), (69377933255426251, 1)] : List FactorBlock).map factorBlockValue).prod) = 18848895370703068715411803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_45280717
      · exact prime_fortySevenAS_69377933255426251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18848895370703068715411803) ^ 9424447685351534357705901 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18848895370703068715411803) ^ 6282965123567689571803934 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18848895370703068715411803) ^ 416267599532557506 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (2 : ZMod 18848895370703068715411803) ^ 271684302 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_54264202688313131418978511 : Nat.Prime 54264202688313131418978511 := by
  apply lucas_primality 54264202688313131418978511 (3 : ZMod 54264202688313131418978511)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (825991, 1), (2189862548474625487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (825991, 1), (2189862548474625487, 1)] : List FactorBlock).map factorBlockValue).prod) = 54264202688313131418978511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_825991
      · exact prime_fortySevenAS_2189862548474625487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54264202688313131418978511) ^ 27132101344156565709489255 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54264202688313131418978511) ^ 18088067562771043806326170 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54264202688313131418978511) ^ 10852840537662626283795702 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54264202688313131418978511) ^ 65695876454238764610 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (3 : ZMod 54264202688313131418978511) ^ 24779730 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_854869900812809947277446081 : Nat.Prime 854869900812809947277446081 := by
  apply lucas_primality 854869900812809947277446081 (109 : ZMod 854869900812809947277446081)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 854869900812809947277446081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (109 : ZMod 854869900812809947277446081) ^ 427434950406404973638723040 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 284956633604269982425815360 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 170973980162561989455489216 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 122124271544687135325349440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 77715445528437267934313280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 50286464753694702781026240 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 44993152674358418277760320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 37168256557078693359888960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 29478272441821032664739520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 27576448413316449912175680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 23104591913859728304795840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 20850485385678291397010880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 19880695367739766215754560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 18188721293889573346328640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 16129620770053017873159360 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 14489320352759490631821120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (109 : ZMod 854869900812809947277446081) ^ 14014260669062458152089280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_882008627822740421794190401 : Nat.Prime 882008627822740421794190401 := by
  apply lucas_primality 882008627822740421794190401 (67 : ZMod 882008627822740421794190401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 882008627822740421794190401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 882008627822740421794190401) ^ 441004313911370210897095200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 294002875940913473931396800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 176401725564548084358838080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 126001232546105774542027200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 80182602529340038344926400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 67846817524826186291860800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 51882860460161201282011200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 46421506727512653778641600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 38348201209684366164964800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 30414090614577255923937600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 28451891220088400703038400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 23838071022236227616059200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 21512405556652205409614400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 20511828554017219111492800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 18766141017505115357323200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 16641672223070573996116800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 14949298776656617318545600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (67 : ZMod 882008627822740421794190401) ^ 14459157833159679045806400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1048425350053446161755358401 : Nat.Prime 1048425350053446161755358401 := by
  apply lucas_primality 1048425350053446161755358401 (79 : ZMod 1048425350053446161755358401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1048425350053446161755358401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1048425350053446161755358401) ^ 524212675026723080877679200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 349475116684482053918452800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 209685070010689232351071680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 149775050007635165965051200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 95311395459404196523214400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 80648103850265089365796800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 61672079414908597750315200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 55180281581760324302913600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 45583710871888963554580800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 36152598277705040060529600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 33820172582369231024366400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 28335820271714761128523200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 25571350001303564920862400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 24381984884963864226868800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 22306922341562684292667200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 17769921187346545114497600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1048425350053446161755358401) ^ 17187300820548297733694400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1068587376016012434096807601 : Nat.Prime 1068587376016012434096807601 := by
  apply lucas_primality 1068587376016012434096807601 (142 : ZMod 1068587376016012434096807601)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1068587376016012434096807601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (142 : ZMod 1068587376016012434096807601) ^ 534293688008006217048403800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 356195792005337478032269200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 213717475203202486819361520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 152655339430858919156686800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 97144306910546584917891600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 62858080942118378476282800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 56241440842948022847200400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 46460320696348366699861200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 36847840552276290830924400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 34470560516645562390219600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 28880739892324660380994800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 26063106732097864246263600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 24850869209674707769693200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 22735901617361966682910800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 20162025962566272341449200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 18111650440949363289776400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (142 : ZMod 1068587376016012434096807601) ^ 17517825836328072690111600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1134011092914951970878244801 : Nat.Prime 1134011092914951970878244801 := by
  apply lucas_primality 1134011092914951970878244801 (79 : ZMod 1134011092914951970878244801)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1134011092914951970878244801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1134011092914951970878244801) ^ 567005546457475985439122400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 378003697638317323626081600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 226802218582990394175648960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 103091917537722906443476800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 87231622531919382375249600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 66706534877350115934014400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 59684794363944840572539200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 49304830126737042212097600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 39103830790170757616491200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 36581002997256515189620800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 30648948457160864077790400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 27658807144267121240932800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 26372350998022138857633600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 24127895593935148316558400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 21396435715376452280721600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 19220526998558507980987200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (79 : ZMod 1134011092914951970878244801) ^ 18590345785491015916036800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1683834653116140805243454401 : Nat.Prime 1683834653116140805243454401 := by
  apply lucas_primality 1683834653116140805243454401 (71 : ZMod 1683834653116140805243454401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1683834653116140805243454401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 1683834653116140805243454401) ^ 841917326558070402621727200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 561278217705380268414484800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 336766930623228161048690880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 240547807588020115034779200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 129525742547395446557188800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 99049097242125929720203200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 88622876479796884486497600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 73210202309397426314932800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 58063263900556579491153600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 54317246874714219523982400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 45509044678814616357931200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 41069137880881483054718400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 39158945421305600121940800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 35826269215237038409435200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 31770465153134732174404800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 28539570391798996699041600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (71 : ZMod 1683834653116140805243454401) ^ 27603846772395750905630400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_1852218118427754885767799841 : Nat.Prime 1852218118427754885767799841 := by
  apply lucas_primality 1852218118427754885767799841 (83 : ZMod 1852218118427754885767799841)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1852218118427754885767799841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 1852218118427754885767799841) ^ 926109059213877442883899920 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 617406039475918295255933280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 370443623685550977153559968 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 264602588346822126538257120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 168383465311614080524345440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 142478316802134991212907680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 108954006966338522692223520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 97485164127776572935147360 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 80531222540337168946426080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 63869590290612237440268960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 59748971562185641476380640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 50059949146696077993724320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 45176051668969631360190240 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 43074839963436160134134880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 39408896136760742250378720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 34947511668448205391845280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 31393527430978896368945760 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 1852218118427754885767799841) ^ 30364231449635325996193440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2222661742113305862921359809 : Nat.Prime 2222661742113305862921359809 := by
  apply lucas_primality 2222661742113305862921359809 (83 : ZMod 2222661742113305862921359809)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2222661742113305862921359809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 2222661742113305862921359809) ^ 1111330871056652931460679904 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 740887247371101954307119936 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 317523106016186551845908544 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 202060158373936896629214528 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 170973980162561989455489216 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 130744808359606227230668224 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 116982196953331887522176832 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 96637467048404602735711296 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 76643508348734684928322752 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 71698765874622769771656768 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 60071938976035293592469184 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 54211262002763557632228288 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 51689807956123392160961856 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 47290675364112890700454464 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 41937014002137846470214336 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 37672232917174675642734912 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (83 : ZMod 2222661742113305862921359809) ^ 36437077739562391195432128 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_2415936676210115068392782401 : Nat.Prime 2415936676210115068392782401 := by
  apply lucas_primality 2415936676210115068392782401 (107 : ZMod 2415936676210115068392782401)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2415936676210115068392782401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 2415936676210115068392782401) ^ 1207968338105057534196391200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 805312225403371689464260800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 483187335242023013678556480 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 345133810887159295484683200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 219630606928192278944798400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 185841282785393466799444800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 142113922130006768728987200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 127154561905795529915409600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 83308161248624657530785600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 77933441168068228012670400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 65295585843516623470075200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 58925284785612562643726400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 56184573865351513218436800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 51402908004470533370059200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 45583710871888963554580800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 40948079257798560481233600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (107 : ZMod 2415936676210115068392782401) ^ 39605519282133033908078400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_4630545296069387214419499601 : Nat.Prime 4630545296069387214419499601 := by
  apply lucas_primality 4630545296069387214419499601 (73 : ZMod 4630545296069387214419499601)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4630545296069387214419499601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 4630545296069387214419499601) ^ 2315272648034693607209749800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 1543515098689795738139833200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 926109059213877442883899920 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 661506470867055316345642800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 420958663279035201310863600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 356195792005337478032269200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 272385017415846306730558800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 243712910319441432337868400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 201328056350842922366065200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 159673975726530593600672400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 149372428905464103690951600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 125149872866740194984310800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 112940129172424078400475600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 107687099908590400335337200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 98522240341901855625946800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 87368779171120513479613200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 78483818577447240922364400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 4630545296069387214419499601) ^ 75910578624088314990483600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_5556654355283264657303399521 : Nat.Prime 5556654355283264657303399521 := by
  apply lucas_primality 5556654355283264657303399521 (199 : ZMod 5556654355283264657303399521)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 5556654355283264657303399521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (199 : ZMod 5556654355283264657303399521) ^ 2778327177641632328651699760 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 1852218118427754885767799840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 1111330871056652931460679904 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 793807765040466379614771360 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 505150395934842241573036320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 427434950406404973638723040 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 326862020899015568076670560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 292455492383329718805442080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 241593667621011506839278240 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 191608770871836712320806880 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 179246914686556924429141920 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 150179847440088233981172960 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 135528155006908894080570720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 129224519890308480402404640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 118226688410282226751136160 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 104842535005344616175535840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 94180582292936689106837280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (199 : ZMod 5556654355283264657303399521) ^ 91092694348905977988580320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_11113308710566529314606799041 : Nat.Prime 11113308710566529314606799041 := by
  apply lucas_primality 11113308710566529314606799041 (73 : ZMod 11113308710566529314606799041)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 11113308710566529314606799041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 11113308710566529314606799041) ^ 5556654355283264657303399520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 3704436236855509771535599680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 2222661742113305862921359808 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 1587615530080932759229542720 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 1010300791869684483146072640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 854869900812809947277446080 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 653724041798031136153341120 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 584910984766659437610884160 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 483187335242023013678556480 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 383217541743673424641613760 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 358493829373113848858283840 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 300359694880176467962345920 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 271056310013817788161141440 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 258449039780616960804809280 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 236453376820564453502272320 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 209685070010689232351071680 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 188361164585873378213674560 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (73 : ZMod 11113308710566529314606799041) ^ 182185388697811955977160640 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_27783271776416323286516997601 : Nat.Prime 27783271776416323286516997601 := by
  apply lucas_primality 27783271776416323286516997601 (101 : ZMod 27783271776416323286516997601)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 27783271776416323286516997601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_11
      · exact prime_fortySevenAS_13
      · exact prime_fortySevenAS_17
      · exact prime_fortySevenAS_19
      · exact prime_fortySevenAS_23
      · exact prime_fortySevenAS_29
      · exact prime_fortySevenAS_31
      · exact prime_fortySevenAS_37
      · exact prime_fortySevenAS_41
      · exact prime_fortySevenAS_43
      · exact prime_fortySevenAS_47
      · exact prime_fortySevenAS_53
      · exact prime_fortySevenAS_59
      · exact prime_fortySevenAS_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 27783271776416323286516997601) ^ 13891635888208161643258498800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 9261090592138774428838999200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 5556654355283264657303399520 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 3969038825202331898073856800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 2525751979674211207865181600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 2137174752032024868193615200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 1634310104495077840383352800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 1462277461916648594027210400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 1207968338105057534196391200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 958043854359183561604034400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 896234573432784622145709600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 750899237200441169905864800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 677640775034544470402853600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 646122599451542402012023200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 591133442051411133755680800 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 524212675026723080877679200 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 470902911464683445534186400 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (101 : ZMod 27783271776416323286516997601) ^ 455463471744529889942901600 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_55566543552832646573033995271 : Nat.Prime 55566543552832646573033995271 := by
  apply lucas_primality 55566543552832646573033995271 (7 : ZMod 55566543552832646573033995271)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (271, 1), (45503, 1), (452599661, 1), (142230192277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (271, 1), (45503, 1), (452599661, 1), (142230192277, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_5
      · exact prime_fortySevenAS_7
      · exact prime_fortySevenAS_271
      · exact prime_fortySevenAS_45503
      · exact prime_fortySevenAS_452599661
      · exact prime_fortySevenAS_142230192277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 55566543552832646573033995271) ^ 27783271776416323286516997635 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 11113308710566529314606799054 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 7938077650404663796147713610 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 205042596135913824992745370 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 1221162199257909293300090 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 122771951331250879070 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (7 : ZMod 55566543552832646573033995271) ^ 390680365843942510 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem prime_fortySevenAS_55566543552832646573033995273 : Nat.Prime 55566543552832646573033995273 := by
  apply lucas_primality 55566543552832646573033995273 (10 : ZMod 55566543552832646573033995273)
  · rw [← fortySevenASFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (10572021223902710535204337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (10572021223902710535204337, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortySevenAS_2
      · exact prime_fortySevenAS_3
      · exact prime_fortySevenAS_73
      · exact prime_fortySevenAS_10572021223902710535204337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 55566543552832646573033995273) ^ 27783271776416323286516997636 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 55566543552832646573033995273) ^ 18522181184277548857677998424 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 55566543552832646573033995273) ^ 761185528120995158534712264 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide
    · change (10 : ZMod 55566543552832646573033995273) ^ 5256 ≠ 1
      rw [← fortySevenASFastPow_eq_pow]
      decide

private theorem phi_fortySevenAS_55566543552832646573033995200 : Nat.totient 55566543552832646573033995200 = 7311854317589950051123200000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_7, prime_fortySevenAS_11, prime_fortySevenAS_13, prime_fortySevenAS_17, prime_fortySevenAS_19, prime_fortySevenAS_23, prime_fortySevenAS_29, prime_fortySevenAS_31, prime_fortySevenAS_37, prime_fortySevenAS_41, prime_fortySevenAS_43, prime_fortySevenAS_47, prime_fortySevenAS_53, prime_fortySevenAS_59, prime_fortySevenAS_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995201 : Nat.totient 55566543552832646573033995201 = 55417571585988610408958074800 := by
  rw [← show ((([(373, 1), (258523477787, 1), (576241538698151, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_373, prime_fortySevenAS_258523477787, prime_fortySevenAS_576241538698151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995202 : Nat.totient 55566543552832646573033995202 = 27783271776416323286516997600 := by
  rw [← show ((([(2, 1), (27783271776416323286516997601, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_27783271776416323286516997601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995203 : Nat.totient 55566543552832646573033995203 = 36958443377732220435474421056 := by
  rw [← show ((([(3, 1), (457, 1), (7607, 1), (5327979091087515805199, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_457, prime_fortySevenAS_7607, prime_fortySevenAS_5327979091087515805199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995204 : Nat.totient 55566543552832646573033995204 = 27391883733465923461635216000 := by
  rw [← show ((([(2, 2), (71, 1), (381757, 1), (10520701, 1), (48715072770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_71, prime_fortySevenAS_381757, prime_fortySevenAS_10520701, prime_fortySevenAS_48715072770383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995205 : Nat.totient 55566543552832646573033995205 = 44453234842266117258427196160 := by
  rw [← show ((([(5, 1), (11113308710566529314606799041, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_11113308710566529314606799041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995206 : Nat.totient 55566543552832646573033995206 = 18517023620512918566566034240 := by
  rw [← show ((([(2, 1), (3, 1), (3593, 1), (7437511, 1), (346559089736443487, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_3593, prime_fortySevenAS_7437511, prime_fortySevenAS_346559089736443487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995207 : Nat.totient 55566543552832646573033995207 = 47628464085599493041340186624 := by
  rw [← show ((([(7, 1), (26215169, 1), (302804748289231467329, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_7, prime_fortySevenAS_26215169, prime_fortySevenAS_302804748289231467329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995208 : Nat.totient 55566543552832646573033995208 = 27783271771043386054573542400 := by
  rw [← show ((([(2, 3), (5170965281, 1), (1343234302814898521, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5170965281, prime_fortySevenAS_1343234302814898521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995209 : Nat.totient 55566543552832646573033995209 = 36937606281037647866032202232 := by
  rw [← show ((([(3, 2), (347, 1), (17792681252908308220632083, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_347, prime_fortySevenAS_17792681252908308220632083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995210 : Nat.totient 55566543552832646573033995210 = 22226617421133058629213598080 := by
  rw [← show ((([(2, 1), (5, 1), (5556654355283264657303399521, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_5556654355283264657303399521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995211 : Nat.totient 55566543552832646573033995211 = 50275631810457569216055583200 := by
  rw [← show ((([(11, 1), (211, 1), (4040990453, 1), (5924482459677647, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_11, prime_fortySevenAS_211, prime_fortySevenAS_4040990453, prime_fortySevenAS_5924482459677647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995212 : Nat.totient 55566543552832646573033995212 = 18522181184277548857677998400 := by
  rw [← show ((([(2, 2), (3, 1), (4630545296069387214419499601, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_4630545296069387214419499601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995213 : Nat.totient 55566543552832646573033995213 = 51292179087216871498819263984 := by
  rw [← show ((([(13, 1), (3428267, 1), (1246795977111482196803, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_13, prime_fortySevenAS_3428267, prime_fortySevenAS_1246795977111482196803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995214 : Nat.totient 55566543552832646573033995214 = 23712025942798522779471840000 := by
  rw [← show ((([(2, 1), (7, 1), (233, 1), (587783349997, 1), (28980918557501, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_7, prime_fortySevenAS_233, prime_fortySevenAS_587783349997, prime_fortySevenAS_28980918557501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995215 : Nat.totient 55566543552832646573033995215 = 29503418001703405675571998080 := by
  rw [← show ((([(3, 1), (5, 1), (431, 1), (467, 1), (18404667383036858516053, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_431, prime_fortySevenAS_467, prime_fortySevenAS_18404667383036858516053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995216 : Nat.totient 55566543552832646573033995216 = 27730944883540837742506500096 := by
  rw [← show ((([(2, 4), (607, 1), (4519, 1), (67429, 1), (4477849, 1), (4193206057, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_607, prime_fortySevenAS_4519, prime_fortySevenAS_67429, prime_fortySevenAS_4477849, prime_fortySevenAS_4193206057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995217 : Nat.totient 55566543552832646573033995217 = 51993879501096230042408923392 := by
  rw [← show ((([(17, 1), (173, 1), (29819, 1), (633614756815087963423, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_17, prime_fortySevenAS_173, prime_fortySevenAS_29819, prime_fortySevenAS_633614756815087963423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995218 : Nat.totient 55566543552832646573033995218 = 18522181184086717575119647872 := by
  rw [← show ((([(2, 1), (3, 2), (97060803977, 1), (31805116698921113, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_97060803977, prime_fortySevenAS_31805116698921113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995219 : Nat.totient 55566543552832646573033995219 = 52351148217333265095587902560 := by
  rw [← show ((([(19, 1), (181, 1), (75272999, 1), (214655483703109979, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_19, prime_fortySevenAS_181, prime_fortySevenAS_75272999, prime_fortySevenAS_214655483703109979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995220 : Nat.totient 55566543552832646573033995220 = 22166054430884739668371051296 := by
  rw [← show ((([(2, 2), (5, 1), (367, 1), (7570373781039870105317983, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_367, prime_fortySevenAS_7570373781039870105317983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995221 : Nat.totient 55566543552832646573033995221 = 31726336566499564178965389120 := by
  rw [← show ((([(3, 1), (7, 1), (1223, 1), (2784581, 1), (776976306864094027, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_7, prime_fortySevenAS_1223, prime_fortySevenAS_2784581, prime_fortySevenAS_776976306864094027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995222 : Nat.totient 55566543552832646573033995222 = 25254354062733325261320683520 := by
  rw [← show ((([(2, 1), (11, 1), (8353, 1), (177889, 1), (1699805095970705953, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_11, prime_fortySevenAS_8353, prime_fortySevenAS_177889, prime_fortySevenAS_1699805095970705953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995223 : Nat.totient 55566543552832646573033995223 = 53150606876622531504641212800 := by
  rw [← show ((([(23, 1), (2415936676210115068392782401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_23, prime_fortySevenAS_2415936676210115068392782401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995224 : Nat.totient 55566543552832646573033995224 = 18496346660831082142825689600 := by
  rw [← show ((([(2, 3), (3, 1), (719, 1), (328381, 1), (1077469, 1), (9101027902511, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_719, prime_fortySevenAS_328381, prime_fortySevenAS_1077469, prime_fortySevenAS_9101027902511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995225 : Nat.totient 55566543552832646573033995225 = 44453234842266117258427196160 := by
  rw [← show ((([(5, 2), (2222661742113305862921359809, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_2222661742113305862921359809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995226 : Nat.totient 55566543552832646573033995226 = 25646096922795661413565774848 := by
  rw [← show ((([(2, 1), (13, 1), (252450449, 1), (8465719750144016849, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_13, prime_fortySevenAS_252450449, prime_fortySevenAS_8465719750144016849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995227 : Nat.totient 55566543552832646573033995227 = 37044320284500998632780814640 := by
  rw [← show ((([(3, 4), (880247, 1), (779334335168194956461, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_880247, prime_fortySevenAS_779334335168194956461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995228 : Nat.totient 55566543552832646573033995228 = 23811739341591041715226772736 := by
  rw [← show ((([(2, 2), (7, 1), (21023, 1), (22349, 1), (80629, 1), (52385523976447, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_7, prime_fortySevenAS_21023, prime_fortySevenAS_22349, prime_fortySevenAS_80629, prime_fortySevenAS_52385523976447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995229 : Nat.totient 55566543552832646573033995229 = 53650455798759626877014001456 := by
  rw [← show ((([(29, 1), (1182909643, 1), (1619809019274659107, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_29, prime_fortySevenAS_1182909643, prime_fortySevenAS_1619809019274659107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995230 : Nat.totient 55566543552832646573033995230 = 14817744947422039086142398720 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1852218118427754885767799841, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_1852218118427754885767799841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995231 : Nat.totient 55566543552832646573033995231 = 53773286842083511853596944120 := by
  rw [← show ((([(31, 1), (68279, 1), (26252129452182504786119, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_31, prime_fortySevenAS_68279, prime_fortySevenAS_26252129452182504786119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995232 : Nat.totient 55566543552832646573033995232 = 27523336200569817734628673920 := by
  rw [← show ((([(2, 5), (107, 1), (98711, 1), (164404641816758219563, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_107, prime_fortySevenAS_98711, prime_fortySevenAS_164404641816758219563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995233 : Nat.totient 55566543552832646573033995233 = 33676693062322816104869088000 := by
  rw [← show ((([(3, 1), (11, 1), (1683834653116140805243454401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_11, prime_fortySevenAS_1683834653116140805243454401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995234 : Nat.totient 55566543552832646573033995234 = 26128376372438396989787393280 := by
  rw [← show ((([(2, 1), (17, 2), (1423, 1), (14843, 1), (58207, 1), (78195856452211, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_17, prime_fortySevenAS_1423, prime_fortySevenAS_14843, prime_fortySevenAS_58207, prime_fortySevenAS_78195856452211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995235 : Nat.totient 55566543552832646573033995235 = 38101138882367670626713152000 := by
  rw [← show ((([(5, 1), (7, 1), (23321, 1), (68076648946483116471401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_7, prime_fortySevenAS_23321, prime_fortySevenAS_68076648946483116471401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995236 : Nat.totient 55566543552832646573033995236 = 18520591369331245035455671680 := by
  rw [← show ((([(2, 2), (3, 2), (18671, 1), (30983, 1), (2668208947267058857, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_18671, prime_fortySevenAS_30983, prime_fortySevenAS_2668208947267058857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995237 : Nat.totient 55566543552832646573033995237 = 54064745078406803631566546832 := by
  rw [← show ((([(37, 1), (2172812415463, 1), (691177233576727, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_37, prime_fortySevenAS_2172812415463, prime_fortySevenAS_691177233576727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995238 : Nat.totient 55566543552832646573033995238 = 26176018776194611443194124192 := by
  rw [← show ((([(2, 1), (19, 1), (307, 1), (443, 1), (1487383, 1), (7228777727467847, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_19, prime_fortySevenAS_307, prime_fortySevenAS_443, prime_fortySevenAS_1487383, prime_fortySevenAS_7228777727467847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995239 : Nat.totient 55566543552832646573033995239 = 34194796030396489904087193600 := by
  rw [← show ((([(3, 1), (13, 2), (16160852801, 1), (6781740207771077, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_13, prime_fortySevenAS_16160852801, prime_fortySevenAS_6781740207771077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995240 : Nat.totient 55566543552832646573033995240 = 22226508977389873973961196800 := by
  rw [← show ((([(2, 3), (5, 1), (211151, 1), (6990227, 1), (941171938028653, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_211151, prime_fortySevenAS_6990227, prime_fortySevenAS_941171938028653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995241 : Nat.totient 55566543552832646573033995241 = 54211250071819687495717025280 := by
  rw [← show ((([(41, 1), (4543753, 1), (298273596753408237817, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_41, prime_fortySevenAS_4543753, prime_fortySevenAS_298273596753408237817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995242 : Nat.totient 55566543552832646573033995242 = 15684874592600266404266545344 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (83, 1), (9073319, 1), (1756789875970627213, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_7, prime_fortySevenAS_83, prime_fortySevenAS_9073319, prime_fortySevenAS_1756789875970627213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995243 : Nat.totient 55566543552832646573033995243 = 54274298351175405134631820800 := by
  rw [← show ((([(43, 1), (19706328241, 1), (65575138255055761, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_43, prime_fortySevenAS_19706328241, prime_fortySevenAS_65575138255055761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995244 : Nat.totient 55566543552832646573033995244 = 24880541889328050704343578640 := by
  rw [← show ((([(2, 2), (11, 1), (67, 1), (18848895370703068715411803, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_11, prime_fortySevenAS_67, prime_fortySevenAS_18848895370703068715411803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995245 : Nat.totient 55566543552832646573033995245 = 29453655441720954226709662848 := by
  rw [← show ((([(3, 2), (5, 1), (163, 1), (1361599, 1), (5563704311400334453, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_163, prime_fortySevenAS_1361599, prime_fortySevenAS_5563704311400334453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995246 : Nat.totient 55566543552832646573033995246 = 26540923970786280336165477120 := by
  rw [← show ((([(2, 1), (23, 1), (773, 1), (822010181, 1), (1901073293018377, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_23, prime_fortySevenAS_773, prime_fortySevenAS_822010181, prime_fortySevenAS_1901073293018377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995247 : Nat.totient 55566543552832646573033995247 = 53845522081251599417044904832 := by
  rw [← show ((([(47, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_47, prime_fortySevenAS_103, prime_fortySevenAS_5009, prime_fortySevenAS_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995248 : Nat.totient 55566543552832646573033995248 = 18522181184272974566271283392 := by
  rw [← show ((([(2, 4), (3, 1), (4108225691527, 1), (281784987228163, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_4108225691527, prime_fortySevenAS_281784987228163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995249 : Nat.totient 55566543552832646573033995249 = 47628465902427982776886281600 := by
  rw [← show ((([(7, 2), (1134011092914951970878244801, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_7, prime_fortySevenAS_1134011092914951970878244801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995250 : Nat.totient 55566543552832646573033995250 = 22226615203390933870256089200 := by
  rw [← show ((([(2, 1), (5, 3), (10022183, 1), (22177421247579552907, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_10022183, prime_fortySevenAS_22177421247579552907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995251 : Nat.totient 55566543552832646573033995251 = 34419610264382003709584640000 := by
  rw [← show ((([(3, 1), (17, 1), (79, 1), (10007, 1), (43987, 1), (294751, 1), (106299833741, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_17, prime_fortySevenAS_79, prime_fortySevenAS_10007, prime_fortySevenAS_43987, prime_fortySevenAS_294751, prime_fortySevenAS_106299833741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995252 : Nat.totient 55566543552832646573033995252 = 25646097024384298418323382400 := by
  rw [← show ((([(2, 2), (13, 1), (1068587376016012434096807601, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_13, prime_fortySevenAS_1068587376016012434096807601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995253 : Nat.totient 55566543552832646573033995253 = 54518118202779200411278636800 := by
  rw [← show ((([(53, 1), (1048425350053446161755358401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_53, prime_fortySevenAS_1048425350053446161755358401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995254 : Nat.totient 55566543552832646573033995254 = 18522181177375609188060639336 := by
  rw [← show ((([(2, 1), (3, 3), (2683619707, 1), (383441090072900243, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_2683619707, prime_fortySevenAS_383441090072900243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995255 : Nat.totient 55566543552832646573033995255 = 40406741445977075149168579200 := by
  rw [← show ((([(5, 1), (11, 1), (7639, 1), (11790363139, 1), (11217265569421, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_11, prime_fortySevenAS_7639, prime_fortySevenAS_11790363139, prime_fortySevenAS_11217265569421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995256 : Nat.totient 55566543552832646573033995256 = 23710239094639260498685701120 := by
  rw [← show ((([(2, 3), (7, 1), (229, 1), (15073789, 1), (287453394624700921, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_7, prime_fortySevenAS_229, prime_fortySevenAS_15073789, prime_fortySevenAS_287453394624700921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995257 : Nat.totient 55566543552832646573033995257 = 35077118118283004209869975552 := by
  rw [← show ((([(3, 1), (19, 1), (2003, 1), (1760923, 1), (276386745458729729, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_19, prime_fortySevenAS_2003, prime_fortySevenAS_1760923, prime_fortySevenAS_276386745458729729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995258 : Nat.totient 55566543552832646573033995258 = 26821134340628833403740039680 := by
  rw [← show ((([(2, 1), (29, 1), (6553, 1), (15750841357, 1), (9281997862381, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_29, prime_fortySevenAS_6553, prime_fortySevenAS_15750841357, prime_fortySevenAS_9281997862381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995259 : Nat.totient 55566543552832646573033995259 = 54010976631814478786662632832 := by
  rw [← show ((([(59, 1), (89, 1), (10582087898082774056948009, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_59, prime_fortySevenAS_89, prime_fortySevenAS_10582087898082774056948009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995260 : Nat.totient 55566543552832646573033995260 = 14817719803148930612944896000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (663001, 1), (5301953, 1), (263458415475257, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_663001, prime_fortySevenAS_5301953, prime_fortySevenAS_263458415475257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995261 : Nat.totient 55566543552832646573033995261 = 54417282595123650445646092800 := by
  rw [← show ((([(61, 1), (269, 1), (1549, 1), (2186149460832290840921, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_61, prime_fortySevenAS_269, prime_fortySevenAS_1549, prime_fortySevenAS_2186149460832290840921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995262 : Nat.totient 55566543552832646573033995262 = 26855125054434423321784634880 := by
  rw [← show ((([(2, 1), (31, 1), (883, 1), (22283, 1), (104393, 1), (436330881251113, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_31, prime_fortySevenAS_883, prime_fortySevenAS_22283, prime_fortySevenAS_104393, prime_fortySevenAS_436330881251113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995263 : Nat.totient 55566543552832646573033995263 = 31752310601618655184590854400 := by
  rw [← show ((([(3, 2), (7, 1), (882008627822740421794190401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_7, prime_fortySevenAS_882008627822740421794190401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995264 : Nat.totient 55566543552832646573033995264 = 27783271776416323286516997120 := by
  rw [← show ((([(2, 10), (54264202688313131418978511, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_54264202688313131418978511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995265 : Nat.totient 55566543552832646573033995265 = 41033755239014877469317411840 := by
  rw [← show ((([(5, 1), (13, 1), (854869900812809947277446081, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_13, prime_fortySevenAS_854869900812809947277446081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995266 : Nat.totient 55566543552832646573033995266 = 16671630228872681240034200000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (101, 1), (8335815114436340620017101, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_11, prime_fortySevenAS_101, prime_fortySevenAS_8335815114436340620017101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995267 : Nat.totient 55566543552832646573033995267 = 55497370728613219751468298240 := by
  rw [← show ((([(1229, 1), (2473, 1), (37243, 1), (2947621, 1), (166540968017, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_1229, prime_fortySevenAS_2473, prime_fortySevenAS_37243, prime_fortySevenAS_2947621, prime_fortySevenAS_166540968017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995268 : Nat.totient 55566543552832646573033995268 = 26145084813199332027643514880 := by
  rw [← show ((([(2, 2), (17, 1), (9323, 1), (24413, 1), (24083671, 1), (149075044969, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_17, prime_fortySevenAS_9323, prime_fortySevenAS_24413, prime_fortySevenAS_24083671, prime_fortySevenAS_149075044969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995269 : Nat.totient 55566543552832646573033995269 = 35433737917721872998734462976 := by
  rw [← show ((([(3, 1), (23, 1), (1341052665409, 1), (600507531266689, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_23, prime_fortySevenAS_1341052665409, prime_fortySevenAS_600507531266689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995270 : Nat.totient 55566543552832646573033995270 = 18980668861003059805865433600 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (271, 1), (45503, 1), (452599661, 1), (142230192277, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_7, prime_fortySevenAS_271, prime_fortySevenAS_45503, prime_fortySevenAS_452599661, prime_fortySevenAS_142230192277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995271 : Nat.totient 55566543552832646573033995271 = 55566543552832646573033995270 := by
  rw [← show ((([(55566543552832646573033995271, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_55566543552832646573033995271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995272 : Nat.totient 55566543552832646573033995272 = 18268452674903883804833092608 := by
  rw [← show ((([(2, 3), (3, 2), (73, 1), (10572021223902710535204337, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_73, prime_fortySevenAS_10572021223902710535204337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995273 : Nat.totient 55566543552832646573033995273 = 55566543552832646573033995272 := by
  rw [← show ((([(55566543552832646573033995273, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_55566543552832646573033995273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995274 : Nat.totient 55566543552832646573033995274 = 26850947220160741968177495744 := by
  rw [← show ((([(2, 1), (37, 1), (149, 1), (5039592195976115234267549, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_37, prime_fortySevenAS_149, prime_fortySevenAS_5039592195976115234267549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995275 : Nat.totient 55566543552832646573033995275 = 29218088561277381931682092800 := by
  rw [← show ((([(3, 1), (5, 2), (71, 1), (433231993, 1), (24086475195090479, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_71, prime_fortySevenAS_433231993, prime_fortySevenAS_24086475195090479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995276 : Nat.totient 55566543552832646573033995276 = 26320994314497602451861190992 := by
  rw [← show ((([(2, 2), (19, 1), (18921397311083, 1), (38640842372147, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_19, prime_fortySevenAS_18921397311083, prime_fortySevenAS_38640842372147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995277 : Nat.totient 55566543552832646573033995277 = 43298563786149865873020264000 := by
  rw [← show ((([(7, 1), (11, 1), (1085509, 1), (25592351, 1), (25976404933139, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_7, prime_fortySevenAS_11, prime_fortySevenAS_1085509, prime_fortySevenAS_25592351, prime_fortySevenAS_25976404933139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995278 : Nat.totient 55566543552832646573033995278 = 17097331356324888095637729792 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (335089, 1), (1093427, 1), (1944324797139467, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_13, prime_fortySevenAS_335089, prime_fortySevenAS_1093427, prime_fortySevenAS_1944324797139467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995279 : Nat.totient 55566543552832646573033995279 = 55508359672544239269151200000 := by
  rw [← show ((([(1913, 1), (3271, 1), (4751, 1), (117541, 1), (15901696384003, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_1913, prime_fortySevenAS_3271, prime_fortySevenAS_4751, prime_fortySevenAS_117541, prime_fortySevenAS_15901696384003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995280 : Nat.totient 55566543552832646573033995280 = 22051604685533585726621361024 := by
  rw [← show ((([(2, 4), (5, 1), (127, 1), (5469147987483528206007283, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_127, prime_fortySevenAS_5469147987483528206007283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995281 : Nat.totient 55566543552832646573033995281 = 36662461725247812111274670592 := by
  rw [← show ((([(3, 3), (97, 1), (110329362133, 1), (192303317786903, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_97, prime_fortySevenAS_110329362133, prime_fortySevenAS_192303317786903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995282 : Nat.totient 55566543552832646573033995282 = 27083506097387237858934986880 := by
  rw [← show ((([(2, 1), (41, 1), (1999, 1), (3163, 1), (107173532234745964573, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_41, prime_fortySevenAS_1999, prime_fortySevenAS_3163, prime_fortySevenAS_107173532234745964573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995283 : Nat.totient 55566543552832646573033995283 = 55566538927510325693552186368 := by
  rw [← show ((([(12109919, 1), (1510405709, 1), (3037935340673, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_12109919, prime_fortySevenAS_1510405709, prime_fortySevenAS_3037935340673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995284 : Nat.totient 55566543552832646573033995284 = 15873869975445744847572028128 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (6947, 1), (95221890149281030134683, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_7, prime_fortySevenAS_6947, prime_fortySevenAS_95221890149281030134683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995285 : Nat.totient 55566543552832646573033995285 = 41837369271586133646618040320 := by
  rw [← show ((([(5, 1), (17, 1), (43159, 1), (12455169721, 1), (1216111607839, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_17, prime_fortySevenAS_43159, prime_fortySevenAS_12455169721, prime_fortySevenAS_1216111607839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995286 : Nat.totient 55566543552832646573033995286 = 27067387868026568080174611168 := by
  rw [← show ((([(2, 1), (43, 1), (389, 1), (1660983546147923912627309, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_43, prime_fortySevenAS_389, prime_fortySevenAS_1660983546147923912627309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995287 : Nat.totient 55566543552832646573033995287 = 35766970529475668439131280000 := by
  rw [← show ((([(3, 1), (29, 1), (1075142701, 1), (594056865485916901, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_29, prime_fortySevenAS_1075142701, prime_fortySevenAS_594056865485916901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995288 : Nat.totient 55566543552832646573033995288 = 25116355888880992626091169280 := by
  rw [← show ((([(2, 3), (11, 1), (179, 1), (415523, 1), (8489509759485751153, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_11, prime_fortySevenAS_179, prime_fortySevenAS_415523, prime_fortySevenAS_8489509759485751153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995289 : Nat.totient 55566543552832646573033995289 = 55566540781070802623053692624 := by
  rw [← show ((([(20047373, 1), (2771761843949960255293, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_20047373, prime_fortySevenAS_2771761843949960255293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995290 : Nat.totient 55566543552832646573033995290 = 14625207614173289619340800000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (167, 1), (251, 1), (419, 1), (1447, 1), (24293949631261601, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_5, prime_fortySevenAS_167, prime_fortySevenAS_251, prime_fortySevenAS_419, prime_fortySevenAS_1447, prime_fortySevenAS_24293949631261601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995291 : Nat.totient 55566543552832646573033995291 = 43342489325755954391036069376 := by
  rw [← show ((([(7, 1), (13, 1), (109, 1), (199, 1), (57993367, 1), (485416005710533, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_7, prime_fortySevenAS_13, prime_fortySevenAS_109, prime_fortySevenAS_199, prime_fortySevenAS_57993367, prime_fortySevenAS_485416005710533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995292 : Nat.totient 55566543552832646573033995292 = 26548486725175050874195853280 := by
  rw [← show ((([(2, 2), (23, 2), (991, 1), (443824039, 1), (59705349323663, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_23, prime_fortySevenAS_991, prime_fortySevenAS_443824039, prime_fortySevenAS_59705349323663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995293 : Nat.totient 55566543552832646573033995293 = 35849380000240032008646787200 := by
  rw [← show ((([(3, 1), (31, 1), (12375911, 1), (903140527, 1), (53456180633, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_31, prime_fortySevenAS_12375911, prime_fortySevenAS_903140527, prime_fortySevenAS_53456180633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995294 : Nat.totient 55566543552832646573033995294 = 27192138312123963287581480600 := by
  rw [← show ((([(2, 1), (47, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_47, prime_fortySevenAS_1222615931, prime_fortySevenAS_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995295 : Nat.totient 55566543552832646573033995295 = 42024848321833201867486354560 := by
  rw [← show ((([(5, 1), (19, 1), (487, 1), (18959, 1), (835511, 1), (75821647671247, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5, prime_fortySevenAS_19, prime_fortySevenAS_487, prime_fortySevenAS_18959, prime_fortySevenAS_835511, prime_fortySevenAS_75821647671247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995296 : Nat.totient 55566543552832646573033995296 = 18522181184271060566055468800 := by
  rw [← show ((([(2, 5), (3, 1), (2896074053861, 1), (199863039150191, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_3, prime_fortySevenAS_2896074053861, prime_fortySevenAS_199863039150191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995297 : Nat.totient 55566543552832646573033995297 = 55566543552823196986913218816 := by
  rw [← show ((([(5883978837713, 1), (9443702141938769, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_5883978837713, prime_fortySevenAS_9443702141938769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995298 : Nat.totient 55566543552832646573033995298 = 23714775501576180290237122560 := by
  rw [← show ((([(2, 1), (7, 2), (257, 1), (3491, 1), (631981455880965713323, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_7, prime_fortySevenAS_257, prime_fortySevenAS_3491, prime_fortySevenAS_631981455880965713323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995299 : Nat.totient 55566543552832646573033995299 = 33676692869814588227992137120 := by
  rw [← show ((([(3, 2), (11, 2), (174936383, 1), (291679132971846877, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_3, prime_fortySevenAS_11, prime_fortySevenAS_174936383, prime_fortySevenAS_291679132971846877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortySevenAS_55566543552832646573033995300 : Nat.totient 55566543552832646573033995300 = 22226617420254903537330380800 := by
  rw [← show ((([(2, 2), (5, 2), (25310612273, 1), (21953851986468161, 1)] : List FactorBlock).map factorBlockValue).prod) = 55566543552832646573033995300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortySevenAS_2, prime_fortySevenAS_5, prime_fortySevenAS_25310612273, prime_fortySevenAS_21953851986468161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortySevenAS : certifiedKill 1 55566543552832646573033995199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortySevenAS_55566543552832646573033995200, phi_fortySevenAS_55566543552832646573033995201, phi_fortySevenAS_55566543552832646573033995202,
    phi_fortySevenAS_55566543552832646573033995203, phi_fortySevenAS_55566543552832646573033995204, phi_fortySevenAS_55566543552832646573033995205,
    phi_fortySevenAS_55566543552832646573033995206, phi_fortySevenAS_55566543552832646573033995207, phi_fortySevenAS_55566543552832646573033995208,
    phi_fortySevenAS_55566543552832646573033995209, phi_fortySevenAS_55566543552832646573033995210, phi_fortySevenAS_55566543552832646573033995211,
    phi_fortySevenAS_55566543552832646573033995212, phi_fortySevenAS_55566543552832646573033995213, phi_fortySevenAS_55566543552832646573033995214,
    phi_fortySevenAS_55566543552832646573033995215, phi_fortySevenAS_55566543552832646573033995216, phi_fortySevenAS_55566543552832646573033995217,
    phi_fortySevenAS_55566543552832646573033995218, phi_fortySevenAS_55566543552832646573033995219, phi_fortySevenAS_55566543552832646573033995220,
    phi_fortySevenAS_55566543552832646573033995221, phi_fortySevenAS_55566543552832646573033995222, phi_fortySevenAS_55566543552832646573033995223,
    phi_fortySevenAS_55566543552832646573033995224, phi_fortySevenAS_55566543552832646573033995225, phi_fortySevenAS_55566543552832646573033995226,
    phi_fortySevenAS_55566543552832646573033995227, phi_fortySevenAS_55566543552832646573033995228, phi_fortySevenAS_55566543552832646573033995229,
    phi_fortySevenAS_55566543552832646573033995230, phi_fortySevenAS_55566543552832646573033995231, phi_fortySevenAS_55566543552832646573033995232,
    phi_fortySevenAS_55566543552832646573033995233, phi_fortySevenAS_55566543552832646573033995234, phi_fortySevenAS_55566543552832646573033995235,
    phi_fortySevenAS_55566543552832646573033995236, phi_fortySevenAS_55566543552832646573033995237, phi_fortySevenAS_55566543552832646573033995238,
    phi_fortySevenAS_55566543552832646573033995239, phi_fortySevenAS_55566543552832646573033995240, phi_fortySevenAS_55566543552832646573033995241,
    phi_fortySevenAS_55566543552832646573033995242, phi_fortySevenAS_55566543552832646573033995243, phi_fortySevenAS_55566543552832646573033995244,
    phi_fortySevenAS_55566543552832646573033995245, phi_fortySevenAS_55566543552832646573033995246, phi_fortySevenAS_55566543552832646573033995247,
    phi_fortySevenAS_55566543552832646573033995248, phi_fortySevenAS_55566543552832646573033995249, phi_fortySevenAS_55566543552832646573033995250,
    phi_fortySevenAS_55566543552832646573033995251, phi_fortySevenAS_55566543552832646573033995252, phi_fortySevenAS_55566543552832646573033995253,
    phi_fortySevenAS_55566543552832646573033995254, phi_fortySevenAS_55566543552832646573033995255, phi_fortySevenAS_55566543552832646573033995256,
    phi_fortySevenAS_55566543552832646573033995257, phi_fortySevenAS_55566543552832646573033995258, phi_fortySevenAS_55566543552832646573033995259,
    phi_fortySevenAS_55566543552832646573033995260, phi_fortySevenAS_55566543552832646573033995261, phi_fortySevenAS_55566543552832646573033995262,
    phi_fortySevenAS_55566543552832646573033995263, phi_fortySevenAS_55566543552832646573033995264, phi_fortySevenAS_55566543552832646573033995265,
    phi_fortySevenAS_55566543552832646573033995266, phi_fortySevenAS_55566543552832646573033995267, phi_fortySevenAS_55566543552832646573033995268,
    phi_fortySevenAS_55566543552832646573033995269, phi_fortySevenAS_55566543552832646573033995270, phi_fortySevenAS_55566543552832646573033995271,
    phi_fortySevenAS_55566543552832646573033995272, phi_fortySevenAS_55566543552832646573033995273, phi_fortySevenAS_55566543552832646573033995274,
    phi_fortySevenAS_55566543552832646573033995275, phi_fortySevenAS_55566543552832646573033995276, phi_fortySevenAS_55566543552832646573033995277,
    phi_fortySevenAS_55566543552832646573033995278, phi_fortySevenAS_55566543552832646573033995279, phi_fortySevenAS_55566543552832646573033995280,
    phi_fortySevenAS_55566543552832646573033995281, phi_fortySevenAS_55566543552832646573033995282, phi_fortySevenAS_55566543552832646573033995283,
    phi_fortySevenAS_55566543552832646573033995284, phi_fortySevenAS_55566543552832646573033995285, phi_fortySevenAS_55566543552832646573033995286,
    phi_fortySevenAS_55566543552832646573033995287, phi_fortySevenAS_55566543552832646573033995288, phi_fortySevenAS_55566543552832646573033995289,
    phi_fortySevenAS_55566543552832646573033995290, phi_fortySevenAS_55566543552832646573033995291, phi_fortySevenAS_55566543552832646573033995292,
    phi_fortySevenAS_55566543552832646573033995293, phi_fortySevenAS_55566543552832646573033995294, phi_fortySevenAS_55566543552832646573033995295,
    phi_fortySevenAS_55566543552832646573033995296, phi_fortySevenAS_55566543552832646573033995297, phi_fortySevenAS_55566543552832646573033995298,
    phi_fortySevenAS_55566543552832646573033995299, phi_fortySevenAS_55566543552832646573033995300]

end TotientTailPeriodKiller
end Erdos249257
