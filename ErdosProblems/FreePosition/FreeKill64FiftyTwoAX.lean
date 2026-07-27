import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 52P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyTwoAXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyTwoAXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyTwoAXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyTwoAXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyTwoAXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyTwoAXFastPow a n * fiftyTwoAXFastPow a n * a
        else fiftyTwoAXFastPow a n * fiftyTwoAXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyTwoAX_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyTwoAX_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyTwoAX_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyTwoAX_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyTwoAX_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyTwoAX_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyTwoAX_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyTwoAX_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyTwoAX_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyTwoAX_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyTwoAX_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyTwoAX_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyTwoAX_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyTwoAX_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyTwoAX_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyTwoAX_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyTwoAX_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyTwoAX_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyTwoAX_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyTwoAX_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyTwoAX_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyTwoAX_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyTwoAX_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyTwoAX_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyTwoAX_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyTwoAX_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyTwoAX_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyTwoAX_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyTwoAX_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyTwoAX_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyTwoAX_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyTwoAX_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyTwoAX_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyTwoAX_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyTwoAX_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyTwoAX_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyTwoAX_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyTwoAX_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyTwoAX_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyTwoAX_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyTwoAX_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyTwoAX_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyTwoAX_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyTwoAX_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyTwoAX_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyTwoAX_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyTwoAX_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyTwoAX_257 : Nat.Prime 257 := by norm_num
private theorem prime_fiftyTwoAX_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyTwoAX_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyTwoAX_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyTwoAX_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyTwoAX_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyTwoAX_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyTwoAX_313 : Nat.Prime 313 := by norm_num
private theorem prime_fiftyTwoAX_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftyTwoAX_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftyTwoAX_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyTwoAX_367 : Nat.Prime 367 := by norm_num
private theorem prime_fiftyTwoAX_373 : Nat.Prime 373 := by norm_num
private theorem prime_fiftyTwoAX_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyTwoAX_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftyTwoAX_401 : Nat.Prime 401 := by norm_num
private theorem prime_fiftyTwoAX_409 : Nat.Prime 409 := by norm_num
private theorem prime_fiftyTwoAX_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyTwoAX_421 : Nat.Prime 421 := by norm_num
private theorem prime_fiftyTwoAX_431 : Nat.Prime 431 := by norm_num
private theorem prime_fiftyTwoAX_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftyTwoAX_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyTwoAX_457 : Nat.Prime 457 := by norm_num
private theorem prime_fiftyTwoAX_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftyTwoAX_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyTwoAX_487 : Nat.Prime 487 := by norm_num
private theorem prime_fiftyTwoAX_499 : Nat.Prime 499 := by norm_num
private theorem prime_fiftyTwoAX_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftyTwoAX_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyTwoAX_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyTwoAX_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyTwoAX_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyTwoAX_563 : Nat.Prime 563 := by norm_num
private theorem prime_fiftyTwoAX_577 : Nat.Prime 577 := by norm_num
private theorem prime_fiftyTwoAX_593 : Nat.Prime 593 := by norm_num
private theorem prime_fiftyTwoAX_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftyTwoAX_607 : Nat.Prime 607 := by norm_num
private theorem prime_fiftyTwoAX_613 : Nat.Prime 613 := by norm_num
private theorem prime_fiftyTwoAX_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftyTwoAX_653 : Nat.Prime 653 := by norm_num
private theorem prime_fiftyTwoAX_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftyTwoAX_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftyTwoAX_683 : Nat.Prime 683 := by norm_num
private theorem prime_fiftyTwoAX_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyTwoAX_719 : Nat.Prime 719 := by norm_num
private theorem prime_fiftyTwoAX_733 : Nat.Prime 733 := by norm_num
private theorem prime_fiftyTwoAX_773 : Nat.Prime 773 := by norm_num
private theorem prime_fiftyTwoAX_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyTwoAX_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftyTwoAX_857 : Nat.Prime 857 := by norm_num
private theorem prime_fiftyTwoAX_863 : Nat.Prime 863 := by norm_num
private theorem prime_fiftyTwoAX_887 : Nat.Prime 887 := by norm_num
private theorem prime_fiftyTwoAX_907 : Nat.Prime 907 := by norm_num
private theorem prime_fiftyTwoAX_929 : Nat.Prime 929 := by norm_num
private theorem prime_fiftyTwoAX_937 : Nat.Prime 937 := by norm_num
private theorem prime_fiftyTwoAX_967 : Nat.Prime 967 := by norm_num
private theorem prime_fiftyTwoAX_971 : Nat.Prime 971 := by norm_num
private theorem prime_fiftyTwoAX_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftyTwoAX_991 : Nat.Prime 991 := by norm_num
private theorem prime_fiftyTwoAX_997 : Nat.Prime 997 := by norm_num
private theorem prime_fiftyTwoAX_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftyTwoAX_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_fiftyTwoAX_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fiftyTwoAX_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fiftyTwoAX_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_fiftyTwoAX_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_fiftyTwoAX_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fiftyTwoAX_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fiftyTwoAX_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fiftyTwoAX_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fiftyTwoAX_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftyTwoAX_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_fiftyTwoAX_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_fiftyTwoAX_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fiftyTwoAX_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_fiftyTwoAX_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fiftyTwoAX_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_fiftyTwoAX_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_fiftyTwoAX_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_fiftyTwoAX_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fiftyTwoAX_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_fiftyTwoAX_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyTwoAX_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_fiftyTwoAX_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_fiftyTwoAX_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_fiftyTwoAX_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_fiftyTwoAX_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fiftyTwoAX_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_fiftyTwoAX_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fiftyTwoAX_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_fiftyTwoAX_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fiftyTwoAX_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fiftyTwoAX_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_fiftyTwoAX_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_fiftyTwoAX_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fiftyTwoAX_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_fiftyTwoAX_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_fiftyTwoAX_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_fiftyTwoAX_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_fiftyTwoAX_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_fiftyTwoAX_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_fiftyTwoAX_2477 : Nat.Prime 2477 := by norm_num
private theorem prime_fiftyTwoAX_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_fiftyTwoAX_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_fiftyTwoAX_2789 : Nat.Prime 2789 := by norm_num
private theorem prime_fiftyTwoAX_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_fiftyTwoAX_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_fiftyTwoAX_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_fiftyTwoAX_3119 : Nat.Prime 3119 := by norm_num
private theorem prime_fiftyTwoAX_3251 : Nat.Prime 3251 := by norm_num
private theorem prime_fiftyTwoAX_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_fiftyTwoAX_3299 : Nat.Prime 3299 := by norm_num
private theorem prime_fiftyTwoAX_3391 : Nat.Prime 3391 := by norm_num
private theorem prime_fiftyTwoAX_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_fiftyTwoAX_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_fiftyTwoAX_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_fiftyTwoAX_3919 : Nat.Prime 3919 := by norm_num
private theorem prime_fiftyTwoAX_4091 : Nat.Prime 4091 := by norm_num
private theorem prime_fiftyTwoAX_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_fiftyTwoAX_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_fiftyTwoAX_4219 : Nat.Prime 4219 := by norm_num
private theorem prime_fiftyTwoAX_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_fiftyTwoAX_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_fiftyTwoAX_4649 : Nat.Prime 4649 := by norm_num
private theorem prime_fiftyTwoAX_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_fiftyTwoAX_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_fiftyTwoAX_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyTwoAX_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_fiftyTwoAX_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_fiftyTwoAX_5647 : Nat.Prime 5647 := by norm_num
private theorem prime_fiftyTwoAX_5791 : Nat.Prime 5791 := by norm_num
private theorem prime_fiftyTwoAX_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_fiftyTwoAX_6203 : Nat.Prime 6203 := by norm_num
private theorem prime_fiftyTwoAX_6247 : Nat.Prime 6247 := by norm_num
private theorem prime_fiftyTwoAX_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fiftyTwoAX_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_fiftyTwoAX_6599 : Nat.Prime 6599 := by norm_num
private theorem prime_fiftyTwoAX_6947 : Nat.Prime 6947 := by norm_num
private theorem prime_fiftyTwoAX_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_fiftyTwoAX_7057 : Nat.Prime 7057 := by norm_num
private theorem prime_fiftyTwoAX_8117 : Nat.Prime 8117 := by norm_num
private theorem prime_fiftyTwoAX_8311 : Nat.Prime 8311 := by norm_num
private theorem prime_fiftyTwoAX_8669 : Nat.Prime 8669 := by norm_num
private theorem prime_fiftyTwoAX_9437 : Nat.Prime 9437 := by norm_num
private theorem prime_fiftyTwoAX_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_fiftyTwoAX_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_fiftyTwoAX_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_fiftyTwoAX_11351 : Nat.Prime 11351 := by norm_num
private theorem prime_fiftyTwoAX_11369 : Nat.Prime 11369 := by norm_num
private theorem prime_fiftyTwoAX_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_fiftyTwoAX_12569 : Nat.Prime 12569 := by norm_num
private theorem prime_fiftyTwoAX_12619 : Nat.Prime 12619 := by norm_num
private theorem prime_fiftyTwoAX_13463 : Nat.Prime 13463 := by norm_num
private theorem prime_fiftyTwoAX_13487 : Nat.Prime 13487 := by norm_num
private theorem prime_fiftyTwoAX_13567 : Nat.Prime 13567 := by norm_num
private theorem prime_fiftyTwoAX_13633 : Nat.Prime 13633 := by norm_num
private theorem prime_fiftyTwoAX_14057 : Nat.Prime 14057 := by norm_num
private theorem prime_fiftyTwoAX_14341 : Nat.Prime 14341 := by norm_num
private theorem prime_fiftyTwoAX_15101 : Nat.Prime 15101 := by norm_num
private theorem prime_fiftyTwoAX_15139 : Nat.Prime 15139 := by norm_num
private theorem prime_fiftyTwoAX_15227 : Nat.Prime 15227 := by norm_num
private theorem prime_fiftyTwoAX_15373 : Nat.Prime 15373 := by norm_num
private theorem prime_fiftyTwoAX_16097 : Nat.Prime 16097 := by norm_num
private theorem prime_fiftyTwoAX_16673 : Nat.Prime 16673 := by norm_num
private theorem prime_fiftyTwoAX_17449 : Nat.Prime 17449 := by norm_num
private theorem prime_fiftyTwoAX_18131 : Nat.Prime 18131 := by norm_num
private theorem prime_fiftyTwoAX_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_fiftyTwoAX_19387 : Nat.Prime 19387 := by norm_num
private theorem prime_fiftyTwoAX_19457 : Nat.Prime 19457 := by norm_num
private theorem prime_fiftyTwoAX_20023 : Nat.Prime 20023 := by norm_num
private theorem prime_fiftyTwoAX_21563 : Nat.Prime 21563 := by norm_num
private theorem prime_fiftyTwoAX_21611 : Nat.Prime 21611 := by norm_num
private theorem prime_fiftyTwoAX_24019 : Nat.Prime 24019 := by norm_num
private theorem prime_fiftyTwoAX_25373 : Nat.Prime 25373 := by norm_num
private theorem prime_fiftyTwoAX_25951 : Nat.Prime 25951 := by norm_num
private theorem prime_fiftyTwoAX_26669 : Nat.Prime 26669 := by norm_num
private theorem prime_fiftyTwoAX_27197 : Nat.Prime 27197 := by norm_num
private theorem prime_fiftyTwoAX_27509 : Nat.Prime 27509 := by norm_num
private theorem prime_fiftyTwoAX_28229 : Nat.Prime 28229 := by norm_num
private theorem prime_fiftyTwoAX_30853 : Nat.Prime 30853 := by norm_num
private theorem prime_fiftyTwoAX_30931 : Nat.Prime 30931 := by norm_num
private theorem prime_fiftyTwoAX_32029 : Nat.Prime 32029 := by norm_num
private theorem prime_fiftyTwoAX_32237 : Nat.Prime 32237 := by norm_num
private theorem prime_fiftyTwoAX_32423 : Nat.Prime 32423 := by norm_num
private theorem prime_fiftyTwoAX_32797 : Nat.Prime 32797 := by norm_num
private theorem prime_fiftyTwoAX_33287 : Nat.Prime 33287 := by norm_num
private theorem prime_fiftyTwoAX_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyTwoAX_36263 : Nat.Prime 36263 := by norm_num
private theorem prime_fiftyTwoAX_36571 : Nat.Prime 36571 := by norm_num
private theorem prime_fiftyTwoAX_36929 : Nat.Prime 36929 := by norm_num
private theorem prime_fiftyTwoAX_37013 : Nat.Prime 37013 := by norm_num
private theorem prime_fiftyTwoAX_37397 : Nat.Prime 37397 := by norm_num
private theorem prime_fiftyTwoAX_39227 : Nat.Prime 39227 := by norm_num
private theorem prime_fiftyTwoAX_39719 : Nat.Prime 39719 := by norm_num
private theorem prime_fiftyTwoAX_39791 : Nat.Prime 39791 := by norm_num
private theorem prime_fiftyTwoAX_40531 : Nat.Prime 40531 := by norm_num
private theorem prime_fiftyTwoAX_43013 : Nat.Prime 43013 := by norm_num
private theorem prime_fiftyTwoAX_43093 : Nat.Prime 43093 := by norm_num
private theorem prime_fiftyTwoAX_44221 : Nat.Prime 44221 := by norm_num
private theorem prime_fiftyTwoAX_44641 : Nat.Prime 44641 := by norm_num
private theorem prime_fiftyTwoAX_46861 : Nat.Prime 46861 := by norm_num
private theorem prime_fiftyTwoAX_47149 : Nat.Prime 47149 := by norm_num
private theorem prime_fiftyTwoAX_49277 : Nat.Prime 49277 := by norm_num
private theorem prime_fiftyTwoAX_49927 : Nat.Prime 49927 := by norm_num
private theorem prime_fiftyTwoAX_52183 : Nat.Prime 52183 := by norm_num
private theorem prime_fiftyTwoAX_52457 : Nat.Prime 52457 := by norm_num
private theorem prime_fiftyTwoAX_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_fiftyTwoAX_54499 : Nat.Prime 54499 := by norm_num
private theorem prime_fiftyTwoAX_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_fiftyTwoAX_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyTwoAX_62981 : Nat.Prime 62981 := by norm_num
private theorem prime_fiftyTwoAX_64091 : Nat.Prime 64091 := by norm_num
private theorem prime_fiftyTwoAX_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_fiftyTwoAX_74323 : Nat.Prime 74323 := by norm_num
private theorem prime_fiftyTwoAX_76259 : Nat.Prime 76259 := by norm_num
private theorem prime_fiftyTwoAX_78233 : Nat.Prime 78233 := by norm_num
private theorem prime_fiftyTwoAX_80833 : Nat.Prime 80833 := by norm_num
private theorem prime_fiftyTwoAX_83423 : Nat.Prime 83423 := by norm_num
private theorem prime_fiftyTwoAX_85247 : Nat.Prime 85247 := by norm_num
private theorem prime_fiftyTwoAX_85469 : Nat.Prime 85469 := by norm_num
private theorem prime_fiftyTwoAX_94651 : Nat.Prime 94651 := by norm_num
private theorem prime_fiftyTwoAX_95083 : Nat.Prime 95083 := by norm_num
private theorem prime_fiftyTwoAX_96211 : Nat.Prime 96211 := by norm_num
private theorem prime_fiftyTwoAX_104161 : Nat.Prime 104161 := by norm_num
private theorem prime_fiftyTwoAX_106277 : Nat.Prime 106277 := by norm_num
private theorem prime_fiftyTwoAX_107053 : Nat.Prime 107053 := by norm_num
private theorem prime_fiftyTwoAX_109849 : Nat.Prime 109849 := by norm_num
private theorem prime_fiftyTwoAX_110923 : Nat.Prime 110923 := by norm_num
private theorem prime_fiftyTwoAX_110947 : Nat.Prime 110947 := by norm_num
private theorem prime_fiftyTwoAX_118691 : Nat.Prime 118691 := by norm_num
private theorem prime_fiftyTwoAX_119653 : Nat.Prime 119653 := by norm_num
private theorem prime_fiftyTwoAX_123427 : Nat.Prime 123427 := by norm_num
private theorem prime_fiftyTwoAX_124001 : Nat.Prime 124001 := by norm_num
private theorem prime_fiftyTwoAX_127691 : Nat.Prime 127691 := by norm_num
private theorem prime_fiftyTwoAX_128257 : Nat.Prime 128257 := by norm_num
private theorem prime_fiftyTwoAX_129593 : Nat.Prime 129593 := by norm_num
private theorem prime_fiftyTwoAX_139939 : Nat.Prime 139939 := by norm_num
private theorem prime_fiftyTwoAX_146173 : Nat.Prime 146173 := by norm_num
private theorem prime_fiftyTwoAX_150343 : Nat.Prime 150343 := by norm_num
private theorem prime_fiftyTwoAX_150377 : Nat.Prime 150377 := by norm_num
private theorem prime_fiftyTwoAX_153929 : Nat.Prime 153929 := by norm_num
private theorem prime_fiftyTwoAX_155203 : Nat.Prime 155203 := by norm_num
private theorem prime_fiftyTwoAX_155609 : Nat.Prime 155609 := by norm_num
private theorem prime_fiftyTwoAX_155693 : Nat.Prime 155693 := by norm_num
private theorem prime_fiftyTwoAX_158759 : Nat.Prime 158759 := by norm_num
private theorem prime_fiftyTwoAX_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_fiftyTwoAX_166931 : Nat.Prime 166931 := by norm_num
private theorem prime_fiftyTwoAX_193883 : Nat.Prime 193883 := by norm_num
private theorem prime_fiftyTwoAX_196751 : Nat.Prime 196751 := by norm_num
private theorem prime_fiftyTwoAX_199109 : Nat.Prime 199109 := by norm_num
private theorem prime_fiftyTwoAX_209623 : Nat.Prime 209623 := by norm_num
private theorem prime_fiftyTwoAX_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fiftyTwoAX_236471 : Nat.Prime 236471 := by norm_num
private theorem prime_fiftyTwoAX_239233 : Nat.Prime 239233 := by norm_num
private theorem prime_fiftyTwoAX_242257 : Nat.Prime 242257 := by norm_num
private theorem prime_fiftyTwoAX_248057 : Nat.Prime 248057 := by norm_num
private theorem prime_fiftyTwoAX_248371 : Nat.Prime 248371 := by norm_num
private theorem prime_fiftyTwoAX_248719 : Nat.Prime 248719 := by norm_num
private theorem prime_fiftyTwoAX_254927 : Nat.Prime 254927 := by norm_num
private theorem prime_fiftyTwoAX_255587 : Nat.Prime 255587 := by norm_num
private theorem prime_fiftyTwoAX_265247 : Nat.Prime 265247 := by norm_num
private theorem prime_fiftyTwoAX_274831 : Nat.Prime 274831 := by norm_num
private theorem prime_fiftyTwoAX_278911 : Nat.Prime 278911 := by norm_num
private theorem prime_fiftyTwoAX_328177 : Nat.Prime 328177 := by norm_num
private theorem prime_fiftyTwoAX_361451 : Nat.Prime 361451 := by norm_num
private theorem prime_fiftyTwoAX_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_fiftyTwoAX_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_fiftyTwoAX_392099 : Nat.Prime 392099 := by norm_num
private theorem prime_fiftyTwoAX_408209 : Nat.Prime 408209 := by norm_num
private theorem prime_fiftyTwoAX_409901 : Nat.Prime 409901 := by norm_num
private theorem prime_fiftyTwoAX_413141 : Nat.Prime 413141 := by norm_num
private theorem prime_fiftyTwoAX_415969 : Nat.Prime 415969 := by norm_num
private theorem prime_fiftyTwoAX_419827 : Nat.Prime 419827 := by norm_num
private theorem prime_fiftyTwoAX_421133 : Nat.Prime 421133 := by norm_num
private theorem prime_fiftyTwoAX_452687 : Nat.Prime 452687 := by norm_num
private theorem prime_fiftyTwoAX_497677 : Nat.Prime 497677 := by norm_num
private theorem prime_fiftyTwoAX_520837 : Nat.Prime 520837 := by norm_num
private theorem prime_fiftyTwoAX_547357 : Nat.Prime 547357 := by norm_num
private theorem prime_fiftyTwoAX_556859 : Nat.Prime 556859 := by norm_num
private theorem prime_fiftyTwoAX_558979 : Nat.Prime 558979 := by norm_num
private theorem prime_fiftyTwoAX_576523 : Nat.Prime 576523 := by norm_num
private theorem prime_fiftyTwoAX_584153 : Nat.Prime 584153 := by norm_num
private theorem prime_fiftyTwoAX_590437 : Nat.Prime 590437 := by norm_num
private theorem prime_fiftyTwoAX_642871 : Nat.Prime 642871 := by norm_num
private theorem prime_fiftyTwoAX_657653 : Nat.Prime 657653 := by norm_num
private theorem prime_fiftyTwoAX_663203 : Nat.Prime 663203 := by norm_num
private theorem prime_fiftyTwoAX_667123 : Nat.Prime 667123 := by norm_num
private theorem prime_fiftyTwoAX_714283 : Nat.Prime 714283 := by norm_num
private theorem prime_fiftyTwoAX_893041 : Nat.Prime 893041 := by norm_num
private theorem prime_fiftyTwoAX_897517 : Nat.Prime 897517 := by norm_num
private theorem prime_fiftyTwoAX_901937 : Nat.Prime 901937 := by norm_num
private theorem prime_fiftyTwoAX_995117 : Nat.Prime 995117 := by norm_num
private theorem prime_fiftyTwoAX_1029563 : Nat.Prime 1029563 := by norm_num
private theorem prime_fiftyTwoAX_1086611 : Nat.Prime 1086611 := by norm_num
private theorem prime_fiftyTwoAX_1093943 : Nat.Prime 1093943 := by norm_num
private theorem prime_fiftyTwoAX_1125419 : Nat.Prime 1125419 := by norm_num
private theorem prime_fiftyTwoAX_1140949 : Nat.Prime 1140949 := by norm_num
private theorem prime_fiftyTwoAX_1243969 : Nat.Prime 1243969 := by norm_num
private theorem prime_fiftyTwoAX_1285429 : Nat.Prime 1285429 := by norm_num
private theorem prime_fiftyTwoAX_1292293 : Nat.Prime 1292293 := by norm_num
private theorem prime_fiftyTwoAX_1296293 : Nat.Prime 1296293 := by norm_num
private theorem prime_fiftyTwoAX_1430543 : Nat.Prime 1430543 := by norm_num
private theorem prime_fiftyTwoAX_1500157 : Nat.Prime 1500157 := by norm_num
private theorem prime_fiftyTwoAX_1508033 : Nat.Prime 1508033 := by norm_num
private theorem prime_fiftyTwoAX_1573057 : Nat.Prime 1573057 := by norm_num
private theorem prime_fiftyTwoAX_1582963 : Nat.Prime 1582963 := by norm_num
private theorem prime_fiftyTwoAX_1584001 : Nat.Prime 1584001 := by norm_num
private theorem prime_fiftyTwoAX_1587871 : Nat.Prime 1587871 := by norm_num
private theorem prime_fiftyTwoAX_1659491 : Nat.Prime 1659491 := by norm_num
private theorem prime_fiftyTwoAX_1739147 : Nat.Prime 1739147 := by norm_num
private theorem prime_fiftyTwoAX_1919789 : Nat.Prime 1919789 := by norm_num
private theorem prime_fiftyTwoAX_1921687 : Nat.Prime 1921687 := by norm_num
private theorem prime_fiftyTwoAX_1939247 : Nat.Prime 1939247 := by norm_num
private theorem prime_fiftyTwoAX_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fiftyTwoAX_2220277 : Nat.Prime 2220277 := by norm_num
private theorem prime_fiftyTwoAX_2273119 : Nat.Prime 2273119 := by norm_num
private theorem prime_fiftyTwoAX_2529421 : Nat.Prime 2529421 := by norm_num
private theorem prime_fiftyTwoAX_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fiftyTwoAX_2596501 : Nat.Prime 2596501 := by norm_num
private theorem prime_fiftyTwoAX_3228259 : Nat.Prime 3228259 := by norm_num
private theorem prime_fiftyTwoAX_3399569 : Nat.Prime 3399569 := by norm_num
private theorem prime_fiftyTwoAX_3684697 : Nat.Prime 3684697 := by norm_num
private theorem prime_fiftyTwoAX_3937057 : Nat.Prime 3937057 := by norm_num
private theorem prime_fiftyTwoAX_3989119 : Nat.Prime 3989119 := by norm_num
private theorem prime_fiftyTwoAX_4553573 : Nat.Prime 4553573 := by norm_num
private theorem prime_fiftyTwoAX_5140117 : Nat.Prime 5140117 := by norm_num
private theorem prime_fiftyTwoAX_5177657 : Nat.Prime 5177657 := by norm_num
private theorem prime_fiftyTwoAX_5309207 : Nat.Prime 5309207 := by norm_num
private theorem prime_fiftyTwoAX_5591029 : Nat.Prime 5591029 := by norm_num
private theorem prime_fiftyTwoAX_6725401 : Nat.Prime 6725401 := by norm_num
private theorem prime_fiftyTwoAX_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyTwoAX_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_fiftyTwoAX_7590001 : Nat.Prime 7590001 := by norm_num
private theorem prime_fiftyTwoAX_7595443 : Nat.Prime 7595443 := by norm_num
private theorem prime_fiftyTwoAX_8429209 : Nat.Prime 8429209 := by norm_num
private theorem prime_fiftyTwoAX_8431793 : Nat.Prime 8431793 := by norm_num
private theorem prime_fiftyTwoAX_8634161 : Nat.Prime 8634161 := by norm_num
private theorem prime_fiftyTwoAX_9017237 : Nat.Prime 9017237 := by norm_num
private theorem prime_fiftyTwoAX_9269333 : Nat.Prime 9269333 := by norm_num
private theorem prime_fiftyTwoAX_10801067 : Nat.Prime 10801067 := by norm_num
private theorem prime_fiftyTwoAX_11185817 : Nat.Prime 11185817 := by norm_num
private theorem prime_fiftyTwoAX_11202857 : Nat.Prime 11202857 := by norm_num
private theorem prime_fiftyTwoAX_12967547 : Nat.Prime 12967547 := by norm_num
private theorem prime_fiftyTwoAX_13875023 : Nat.Prime 13875023 := by norm_num
private theorem prime_fiftyTwoAX_14990197 : Nat.Prime 14990197 := by norm_num
private theorem prime_fiftyTwoAX_17497079 : Nat.Prime 17497079 := by norm_num
private theorem prime_fiftyTwoAX_19773401 : Nat.Prime 19773401 := by norm_num
private theorem prime_fiftyTwoAX_19965307 : Nat.Prime 19965307 := by norm_num
private theorem prime_fiftyTwoAX_22316617 : Nat.Prime 22316617 := by norm_num
private theorem prime_fiftyTwoAX_23213591 : Nat.Prime 23213591 := by norm_num
private theorem prime_fiftyTwoAX_25037521 : Nat.Prime 25037521 := by norm_num
private theorem prime_fiftyTwoAX_26281223 : Nat.Prime 26281223 := by norm_num
private theorem prime_fiftyTwoAX_26828093 : Nat.Prime 26828093 := by norm_num
private theorem prime_fiftyTwoAX_27509047 : Nat.Prime 27509047 := by norm_num
private theorem prime_fiftyTwoAX_30974893 : Nat.Prime 30974893 := by
  apply lucas_primality 30974893 (2 : ZMod 30974893)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (181, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (181, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 30974893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_181
      · exact prime_fiftyTwoAX_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30974893) ^ 15487446 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30974893) ^ 10324964 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30974893) ^ 2382684 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30974893) ^ 171132 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30974893) ^ 28236 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_34604239 : Nat.Prime 34604239 := by
  apply lucas_primality 34604239 (6 : ZMod 34604239)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1367, 1), (4219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1367, 1), (4219, 1)] : List FactorBlock).map factorBlockValue).prod) = 34604239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_1367
      · exact prime_fiftyTwoAX_4219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 34604239) ^ 17302119 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 34604239) ^ 11534746 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 34604239) ^ 25314 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 34604239) ^ 8202 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_36729659 : Nat.Prime 36729659 := by
  apply lucas_primality 36729659 (2 : ZMod 36729659)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (83, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (83, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 36729659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_73
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36729659) ^ 18364829 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 36729659) ^ 5247094 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 36729659) ^ 503146 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 36729659) ^ 442526 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 36729659) ^ 84826 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_36769511 : Nat.Prime 36769511 := by
  apply lucas_primality 36769511 (14 : ZMod 36769511)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (78233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (78233, 1)] : List FactorBlock).map factorBlockValue).prod) = 36769511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_78233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 36769511) ^ 18384755 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 36769511) ^ 7353902 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 36769511) ^ 782330 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 36769511) ^ 470 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_37044599 : Nat.Prime 37044599 := by
  apply lucas_primality 37044599 (7 : ZMod 37044599)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (64091, 1)] : List FactorBlock).map factorBlockValue).prod) = 37044599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_64091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 37044599) ^ 18522299 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 37044599) ^ 2179094 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 37044599) ^ 578 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_39198199 : Nat.Prime 39198199 := by
  apply lucas_primality 39198199 (6 : ZMod 39198199)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 39198199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_43
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39198199) ^ 19599099 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 13066066 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 3015246 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1351662 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1264458 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 911586 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_39891191 : Nat.Prime 39891191 := by
  apply lucas_primality 39891191 (7 : ZMod 39891191)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3989119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3989119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39891191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_3989119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 39891191) ^ 19945595 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39891191) ^ 7978238 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39891191) ^ 10 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_52689557 : Nat.Prime 52689557 := by
  apply lucas_primality 52689557 (2 : ZMod 52689557)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (677, 1), (19457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (677, 1), (19457, 1)] : List FactorBlock).map factorBlockValue).prod) = 52689557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_677
      · exact prime_fiftyTwoAX_19457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52689557) ^ 26344778 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52689557) ^ 77828 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52689557) ^ 2708 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_57201323 : Nat.Prime 57201323 := by
  apply lucas_primality 57201323 (2 : ZMod 57201323)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (857, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (857, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 57201323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_857
      · exact prime_fiftyTwoAX_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57201323) ^ 28600661 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201323) ^ 2487014 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201323) ^ 66746 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57201323) ^ 39422 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_68392019 : Nat.Prime 68392019 := by
  apply lucas_primality 68392019 (2 : ZMod 68392019)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) = 68392019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_36263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68392019) ^ 34196009 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 2973566 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1668098 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1886 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_1901
      · exact prime_fiftyTwoAX_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_79782383 : Nat.Prime 79782383 := by
  apply lucas_primality 79782383 (5 : ZMod 79782383)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39891191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39891191, 1)] : List FactorBlock).map factorBlockValue).prod) = 79782383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_39891191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 79782383) ^ 39891191 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 79782383) ^ 2 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_83511149 : Nat.Prime 83511149 := by
  apply lucas_primality 83511149 (2 : ZMod 83511149)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) = 83511149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_96211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83511149) ^ 41755574 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 11930164 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 2693908 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 868 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_112714183 : Nat.Prime 112714183 := by
  apply lucas_primality 112714183 (3 : ZMod 112714183)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (101, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (101, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 112714183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_101
      · exact prime_fiftyTwoAX_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112714183) ^ 56357091 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 112714183) ^ 37571394 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 112714183) ^ 16102026 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 112714183) ^ 6630246 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 112714183) ^ 1115982 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 112714183) ^ 216342 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_115231517 : Nat.Prime 115231517 := by
  apply lucas_primality 115231517 (2 : ZMod 115231517)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (577, 1), (49927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (577, 1), (49927, 1)] : List FactorBlock).map factorBlockValue).prod) = 115231517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_577
      · exact prime_fiftyTwoAX_49927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115231517) ^ 57615758 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 115231517) ^ 199708 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 115231517) ^ 2308 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_119596097 : Nat.Prime 119596097 := by
  apply lucas_primality 119596097 (3 : ZMod 119596097)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1367, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1367, 2)] : List FactorBlock).map factorBlockValue).prod) = 119596097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 119596097) ^ 59798048 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 119596097) ^ 87488 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_120491003 : Nat.Prime 120491003 := by
  apply lucas_primality 120491003 (2 : ZMod 120491003)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1663, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1663, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 120491003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_1663
      · exact prime_fiftyTwoAX_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120491003) ^ 60245501 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 7087706 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 72454 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 56542 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_148272073 : Nat.Prime 148272073 := by
  apply lucas_primality 148272073 (5 : ZMod 148272073)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 148272073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_67
      · exact prime_fiftyTwoAX_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 148272073) ^ 74136036 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 49424024 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 11405544 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 3616392 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 2213016 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 857064 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_164681581 : Nat.Prime 164681581 := by
  apply lucas_primality 164681581 (10 : ZMod 164681581)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) = 164681581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_392099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 164681581) ^ 82340790 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 54893860 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 32936316 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 23525940 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 420 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_174255157 : Nat.Prime 174255157 := by
  apply lucas_primality 174255157 (2 : ZMod 174255157)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (373, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (373, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) = 174255157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_373
      · exact prime_fiftyTwoAX_683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174255157) ^ 87127578 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 174255157) ^ 58085052 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 174255157) ^ 9171324 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 174255157) ^ 467172 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 174255157) ^ 255132 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_183112561 : Nat.Prime 183112561 := by
  apply lucas_primality 183112561 (43 : ZMod 183112561)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (41, 1), (6203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (41, 1), (6203, 1)] : List FactorBlock).map factorBlockValue).prod) = 183112561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_6203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 183112561) ^ 91556280 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (43 : ZMod 183112561) ^ 61037520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (43 : ZMod 183112561) ^ 36622512 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (43 : ZMod 183112561) ^ 4466160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (43 : ZMod 183112561) ^ 29520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_190680953 : Nat.Prime 190680953 := by
  apply lucas_primality 190680953 (5 : ZMod 190680953)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (11, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (11, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) = 190680953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_44221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 190680953) ^ 95340476 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 190680953) ^ 27240136 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 190680953) ^ 17334632 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 190680953) ^ 4312 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_200438423 : Nat.Prime 200438423 := by
  apply lucas_primality 200438423 (10 : ZMod 200438423)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (106277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (106277, 1)] : List FactorBlock).map factorBlockValue).prod) = 200438423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_106277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 200438423) ^ 100219211 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 8714714 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 4888742 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 1886 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_210138469 : Nat.Prime 210138469 := by
  apply lucas_primality 210138469 (6 : ZMod 210138469)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3547, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3547, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 210138469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_3547
      · exact prime_fiftyTwoAX_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 210138469) ^ 105069234 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 70046156 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 59244 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 42564 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_215950457 : Nat.Prime 215950457 := by
  apply lucas_primality 215950457 (3 : ZMod 215950457)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1587871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1587871, 1)] : List FactorBlock).map factorBlockValue).prod) = 215950457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_1587871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 215950457) ^ 107975228 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215950457) ^ 12702968 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 215950457) ^ 136 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_220118471 : Nat.Prime 220118471 := by
  apply lucas_primality 220118471 (11 : ZMod 220118471)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) = 220118471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_153929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220118471) ^ 110059235 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 44023694 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 20010770 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 16932190 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 1430 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_191
      · exact prime_fiftyTwoAX_383
      · exact prime_fiftyTwoAX_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_237317393 : Nat.Prime 237317393 := by
  apply lucas_primality 237317393 (3 : ZMod 237317393)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1140949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1140949, 1)] : List FactorBlock).map factorBlockValue).prod) = 237317393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_1140949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 237317393) ^ 118658696 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 237317393) ^ 18255184 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 237317393) ^ 208 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_243182789 : Nat.Prime 243182789 := by
  apply lucas_primality 243182789 (2 : ZMod 243182789)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7013, 1), (8669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7013, 1), (8669, 1)] : List FactorBlock).map factorBlockValue).prod) = 243182789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7013
      · exact prime_fiftyTwoAX_8669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 243182789) ^ 121591394 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243182789) ^ 34676 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243182789) ^ 28052 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_250352849 : Nat.Prime 250352849 := by
  apply lucas_primality 250352849 (3 : ZMod 250352849)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (863, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (863, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) = 250352849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_863
      · exact prime_fiftyTwoAX_18131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 250352849) ^ 125176424 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 250352849) ^ 290096 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 250352849) ^ 13808 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_262731361 : Nat.Prime 262731361 := by
  apply lucas_primality 262731361 (11 : ZMod 262731361)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (547357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (547357, 1)] : List FactorBlock).map factorBlockValue).prod) = 262731361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_547357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 262731361) ^ 131365680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 262731361) ^ 87577120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 262731361) ^ 52546272 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 262731361) ^ 480 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_67
      · exact prime_fiftyTwoAX_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_293837273 : Nat.Prime 293837273 := by
  apply lucas_primality 293837273 (3 : ZMod 293837273)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (36729659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (36729659, 1)] : List FactorBlock).map factorBlockValue).prod) = 293837273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_36729659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 293837273) ^ 146918636 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 293837273) ^ 8 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_360347051 : Nat.Prime 360347051 := by
  apply lucas_primality 360347051 (2 : ZMod 360347051)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) = 360347051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_1029563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 360347051) ^ 180173525 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 72069410 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 51478150 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 350 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_440144753 : Nat.Prime 440144753 := by
  apply lucas_primality 440144753 (3 : ZMod 440144753)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) = 440144753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_27509047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 440144753) ^ 220072376 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 440144753) ^ 16 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_456068273 : Nat.Prime 456068273 := by
  apply lucas_primality 456068273 (3 : ZMod 456068273)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) = 456068273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_191
      · exact prime_fiftyTwoAX_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456068273) ^ 228034136 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 41460752 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 2387792 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 33616 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_480173767 : Nat.Prime 480173767 := by
  apply lucas_primality 480173767 (5 : ZMod 480173767)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (584153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (584153, 1)] : List FactorBlock).map factorBlockValue).prod) = 480173767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_137
      · exact prime_fiftyTwoAX_584153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 480173767) ^ 240086883 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 480173767) ^ 160057922 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 480173767) ^ 3504918 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 480173767) ^ 822 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_508736671 : Nat.Prime 508736671 := by
  apply lucas_primality 508736671 (3 : ZMod 508736671)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (401, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (401, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 508736671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_401
      · exact prime_fiftyTwoAX_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 508736671) ^ 254368335 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 169578890 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 101747334 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 39133590 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 1268670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 156390 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_568369453 : Nat.Prime 568369453 := by
  apply lucas_primality 568369453 (5 : ZMod 568369453)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (61, 1), (110923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (61, 1), (110923, 1)] : List FactorBlock).map factorBlockValue).prod) = 568369453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_110923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 568369453) ^ 284184726 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 568369453) ^ 189456484 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 568369453) ^ 81195636 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 568369453) ^ 9317532 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 568369453) ^ 5124 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_693751151 : Nat.Prime 693751151 := by
  apply lucas_primality 693751151 (7 : ZMod 693751151)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13875023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13875023, 1)] : List FactorBlock).map factorBlockValue).prod) = 693751151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_13875023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 693751151) ^ 346875575 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 693751151) ^ 138750230 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 693751151) ^ 50 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_752335981 : Nat.Prime 752335981 := by
  apply lucas_primality 752335981 (6 : ZMod 752335981)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 752335981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 752335981) ^ 376167990 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 250778660 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 150467196 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 68394180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 32710260 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 25942620 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 440220 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1160494157 : Nat.Prime 1160494157 := by
  apply lucas_primality 1160494157 (2 : ZMod 1160494157)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160494157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_521
      · exact prime_fiftyTwoAX_556859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1160494157) ^ 580247078 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2227436 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2084 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1161774641 : Nat.Prime 1161774641 := by
  apply lucas_primality 1161774641 (3 : ZMod 1161774641)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (67, 1), (16673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (67, 1), (16673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1161774641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_67
      · exact prime_fiftyTwoAX_16673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1161774641) ^ 580887320 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161774641) ^ 232354928 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161774641) ^ 89367280 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161774641) ^ 17339920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1161774641) ^ 69680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1317915923 : Nat.Prime 1317915923 := by
  apply lucas_primality 1317915923 (2 : ZMod 1317915923)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317915923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_313
      · exact prime_fiftyTwoAX_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1317915923) ^ 658957961 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 77524466 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 22337558 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 4210594 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 627878 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1474306679 : Nat.Prime 1474306679 := by
  apply lucas_primality 1474306679 (17 : ZMod 1474306679)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474306679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_127
      · exact prime_fiftyTwoAX_457
      · exact prime_fiftyTwoAX_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1474306679) ^ 737153339 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 113408206 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 11608714 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 3226054 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 1509014 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1518372857 : Nat.Prime 1518372857 := by
  apply lucas_primality 1518372857 (5 : ZMod 1518372857)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 3), (13, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 3), (13, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1518372857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1518372857) ^ 759186428 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 216910408 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 138033896 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 116797912 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 968968 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1595647661 : Nat.Prime 1595647661 := by
  apply lucas_primality 1595647661 (2 : ZMod 1595647661)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79782383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79782383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1595647661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_79782383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1595647661) ^ 797823830 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595647661) ^ 319129532 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595647661) ^ 20 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1855533307 : Nat.Prime 1855533307 := by
  apply lucas_primality 1855533307 (2 : ZMod 1855533307)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (150343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (150343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1855533307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_150343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1855533307) ^ 927766653 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 618511102 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 168684846 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 109149018 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 12342 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1908980081 : Nat.Prime 1908980081 := by
  apply lucas_primality 1908980081 (3 : ZMod 1908980081)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (67, 1), (83, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (67, 1), (83, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908980081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_67
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1908980081) ^ 954490040 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 381796016 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 272711440 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 28492240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 22999760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 3114160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1920695069 : Nat.Prime 1920695069 := by
  apply lucas_primality 1920695069 (2 : ZMod 1920695069)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (480173767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (480173767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1920695069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_480173767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1920695069) ^ 960347534 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1920695069) ^ 4 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_4113721823 : Nat.Prime 4113721823 := by
  apply lucas_primality 4113721823 (5 : ZMod 4113721823)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (293837273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (293837273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4113721823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_293837273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4113721823) ^ 2056860911 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113721823) ^ 587674546 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4113721823) ^ 14 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_4499780951 : Nat.Prime 4499780951 := by
  apply lucas_primality 4499780951 (7 : ZMod 4499780951)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4499780951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_558979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4499780951) ^ 2249890475 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 899956190 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 642825850 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 195642650 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 8050 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_4896040421 : Nat.Prime 4896040421 := by
  apply lucas_primality 4896040421 (2 : ZMod 4896040421)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (41, 1), (227, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (41, 1), (227, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) = 4896040421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_227
      · exact prime_fiftyTwoAX_907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4896040421) ^ 2448020210 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4896040421) ^ 979208084 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4896040421) ^ 168828980 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4896040421) ^ 119415620 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4896040421) ^ 21568460 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4896040421) ^ 5398060 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_5327453741 : Nat.Prime 5327453741 := by
  apply lucas_primality 5327453741 (2 : ZMod 5327453741)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5327453741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_499
      · exact prime_fiftyTwoAX_76259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5327453741) ^ 2663726870 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 1065490748 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 761064820 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 10676260 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 69860 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_5834431507 : Nat.Prime 5834431507 := by
  apply lucas_primality 5834431507 (2 : ZMod 5834431507)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5834431507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_26281223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5834431507) ^ 2917215753 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 1944810502 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 157687338 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 222 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6273351317 : Nat.Prime 6273351317 := by
  apply lucas_primality 6273351317 (2 : ZMod 6273351317)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (997, 1), (1573057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (997, 1), (1573057, 1)] : List FactorBlock).map factorBlockValue).prod) = 6273351317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_997
      · exact prime_fiftyTwoAX_1573057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6273351317) ^ 3136675658 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6273351317) ^ 6292228 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6273351317) ^ 3988 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6678008737 : Nat.Prime 6678008737 := by
  apply lucas_primality 6678008737 (17 : ZMod 6678008737)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (19, 1), (563, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (19, 1), (563, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 6678008737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_563
      · exact prime_fiftyTwoAX_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 6678008737) ^ 3339004368 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 6678008737) ^ 2226002912 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 6678008737) ^ 954001248 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 6678008737) ^ 351474144 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 6678008737) ^ 11861472 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 6678008737) ^ 7188384 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6820433437 : Nat.Prime 6820433437 := by
  apply lucas_primality 6820433437 (5 : ZMod 6820433437)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (568369453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (568369453, 1)] : List FactorBlock).map factorBlockValue).prod) = 6820433437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_568369453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6820433437) ^ 3410216718 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820433437) ^ 2273477812 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 6820433437) ^ 12 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6856826173 : Nat.Prime 6856826173 := by
  apply lucas_primality 6856826173 (14 : ZMod 6856826173)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (17, 1), (19, 1), (79, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (17, 1), (19, 1), (79, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 6856826173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_79
      · exact prime_fiftyTwoAX_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 6856826173) ^ 3428413086 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 2285608724 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 979546596 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 403342716 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 360885588 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 86795268 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 6856826173) ^ 15003996 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6864158761 : Nat.Prime 6864158761 := by
  apply lucas_primality 6864158761 (7 : ZMod 6864158761)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (57201323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (57201323, 1)] : List FactorBlock).map factorBlockValue).prod) = 6864158761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_57201323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6864158761) ^ 3432079380 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6864158761) ^ 2288052920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6864158761) ^ 1372831752 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6864158761) ^ 120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_7465557739 : Nat.Prime 7465557739 := by
  apply lucas_primality 7465557739 (2 : ZMod 7465557739)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (241, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (241, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) = 7465557739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_241
      · exact prime_fiftyTwoAX_109849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7465557739) ^ 3732778869 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7465557739) ^ 2488519246 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7465557739) ^ 158841654 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7465557739) ^ 30977418 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7465557739) ^ 67962 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_8765300881 : Nat.Prime 8765300881 := by
  apply lucas_primality 8765300881 (11 : ZMod 8765300881)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (1739147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (1739147, 1)] : List FactorBlock).map factorBlockValue).prod) = 8765300881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_1739147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8765300881) ^ 4382650440 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 8765300881) ^ 2921766960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 8765300881) ^ 1753060176 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 8765300881) ^ 1252185840 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 8765300881) ^ 5040 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_9501820109 : Nat.Prime 9501820109 := by
  apply lucas_primality 9501820109 (2 : ZMod 9501820109)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (215950457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (215950457, 1)] : List FactorBlock).map factorBlockValue).prod) = 9501820109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_215950457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9501820109) ^ 4750910054 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9501820109) ^ 863801828 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9501820109) ^ 44 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_9625718593 : Nat.Prime 9625718593 := by
  apply lucas_primality 9625718593 (10 : ZMod 9625718593)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (7, 1), (19, 1), (23, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (7, 1), (19, 1), (23, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 9625718593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9625718593) ^ 4812859296 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625718593) ^ 3208572864 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625718593) ^ 1375102656 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625718593) ^ 506616768 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625718593) ^ 418509504 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 9625718593) ^ 15857856 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_9792080843 : Nat.Prime 9792080843 := by
  apply lucas_primality 9792080843 (2 : ZMod 9792080843)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4896040421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4896040421, 1)] : List FactorBlock).map factorBlockValue).prod) = 9792080843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_4896040421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9792080843) ^ 4896040421 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9792080843) ^ 2 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_11381553479 : Nat.Prime 11381553479 := by
  apply lucas_primality 11381553479 (7 : ZMod 11381553479)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36571, 1), (155609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36571, 1), (155609, 1)] : List FactorBlock).map factorBlockValue).prod) = 11381553479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_36571
      · exact prime_fiftyTwoAX_155609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 11381553479) ^ 5690776739 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11381553479) ^ 311218 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11381553479) ^ 73142 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_11928834361 : Nat.Prime 11928834361 := by
  apply lucas_primality 11928834361 (7 : ZMod 11928834361)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11928834361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_211
      · exact prime_fiftyTwoAX_17449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11928834361) ^ 5964417180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 3976278120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 2385766872 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 56534760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 683640 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_13001360959 : Nat.Prime 13001360959 := by
  apply lucas_primality 13001360959 (3 : ZMod 13001360959)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) = 13001360959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_229
      · exact prime_fiftyTwoAX_85247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13001360959) ^ 6500680479 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 4333786986 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 351388134 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 56774502 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 152514 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_14147943049 : Nat.Prime 14147943049 := by
  apply lucas_primality 14147943049 (13 : ZMod 14147943049)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (313, 1), (36929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (313, 1), (36929, 1)] : List FactorBlock).map factorBlockValue).prod) = 14147943049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_313
      · exact prime_fiftyTwoAX_36929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 14147943049) ^ 7073971524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 14147943049) ^ 4715981016 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 14147943049) ^ 832231944 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 14147943049) ^ 45201096 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 14147943049) ^ 383112 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_17499900673 : Nat.Prime 17499900673 := by
  apply lucas_primality 17499900673 (5 : ZMod 17499900673)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (7595443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (7595443, 1)] : List FactorBlock).map factorBlockValue).prod) = 17499900673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7595443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17499900673) ^ 8749950336 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17499900673) ^ 5833300224 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17499900673) ^ 2304 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_19167809209 : Nat.Prime 19167809209 := by
  apply lucas_primality 19167809209 (7 : ZMod 19167809209)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) = 19167809209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_3011
      · exact prime_fiftyTwoAX_265247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19167809209) ^ 9583904604 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6389269736 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6365928 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 72264 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_23111364013 : Nat.Prime 23111364013 := by
  apply lucas_primality 23111364013 (2 : ZMod 23111364013)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (307, 1), (331, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (307, 1), (331, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) = 23111364013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_307
      · exact prime_fiftyTwoAX_331
      · exact prime_fiftyTwoAX_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23111364013) ^ 11555682006 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 7703788004 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 2101033092 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 75281316 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 69822852 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 13413444 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_23210693491 : Nat.Prime 23210693491 := by
  apply lucas_primality 23210693491 (10 : ZMod 23210693491)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3119, 1), (248057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3119, 1), (248057, 1)] : List FactorBlock).map factorBlockValue).prod) = 23210693491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_3119
      · exact prime_fiftyTwoAX_248057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 23210693491) ^ 11605346745 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 7736897830 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 4642138698 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 7441710 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 93570 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_24580164613 : Nat.Prime 24580164613 := by
  apply lucas_primality 24580164613 (2 : ZMod 24580164613)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (120491003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (120491003, 1)] : List FactorBlock).map factorBlockValue).prod) = 24580164613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_120491003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24580164613) ^ 12290082306 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 8193388204 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 1445892036 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 204 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_29486133581 : Nat.Prime 29486133581 := by
  apply lucas_primality 29486133581 (2 : ZMod 29486133581)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) = 29486133581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_1474306679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29486133581) ^ 14743066790 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 5897226716 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 20 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_36699648137 : Nat.Prime 36699648137 := by
  apply lucas_primality 36699648137 (3 : ZMod 36699648137)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (97, 1), (313, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (97, 1), (313, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) = 36699648137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_97
      · exact prime_fiftyTwoAX_313
      · exact prime_fiftyTwoAX_2477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36699648137) ^ 18349824068 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 601633576 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 378346888 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 117251272 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 14816168 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_44619343003 : Nat.Prime 44619343003 := by
  apply lucas_primality 44619343003 (3 : ZMod 44619343003)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (190680953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (190680953, 1)] : List FactorBlock).map factorBlockValue).prod) = 44619343003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_190680953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44619343003) ^ 22309671501 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44619343003) ^ 14873114334 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44619343003) ^ 3432257154 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 44619343003) ^ 234 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_151
      · exact prime_fiftyTwoAX_479
      · exact prime_fiftyTwoAX_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_45063512821 : Nat.Prime 45063512821 := by
  apply lucas_primality 45063512821 (7 : ZMod 45063512821)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (250352849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (250352849, 1)] : List FactorBlock).map factorBlockValue).prod) = 45063512821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_250352849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 45063512821) ^ 22531756410 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 45063512821) ^ 15021170940 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 45063512821) ^ 9012702564 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 45063512821) ^ 180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_50754978959 : Nat.Prime 50754978959 := by
  apply lucas_primality 50754978959 (11 : ZMod 50754978959)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (103, 1), (12967547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (103, 1), (12967547, 1)] : List FactorBlock).map factorBlockValue).prod) = 50754978959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_103
      · exact prime_fiftyTwoAX_12967547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 50754978959) ^ 25377489479 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 50754978959) ^ 2671314682 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 50754978959) ^ 492766786 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 50754978959) ^ 3914 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_64809180617 : Nat.Prime 64809180617 := by
  apply lucas_primality 64809180617 (3 : ZMod 64809180617)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (463, 1), (17497079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (463, 1), (17497079, 1)] : List FactorBlock).map factorBlockValue).prod) = 64809180617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_463
      · exact prime_fiftyTwoAX_17497079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64809180617) ^ 32404590308 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64809180617) ^ 139976632 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 64809180617) ^ 3704 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_72863556869 : Nat.Prime 72863556869 := by
  apply lucas_primality 72863556869 (2 : ZMod 72863556869)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) = 72863556869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_73
      · exact prime_fiftyTwoAX_5309207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72863556869) ^ 36431778434 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 1550288444 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 998130916 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 13724 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_77681756927 : Nat.Prime 77681756927 := by
  apply lucas_primality 77681756927 (5 : ZMod 77681756927)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6947, 1), (5591029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6947, 1), (5591029, 1)] : List FactorBlock).map factorBlockValue).prod) = 77681756927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_6947
      · exact prime_fiftyTwoAX_5591029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 77681756927) ^ 38840878463 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 77681756927) ^ 11182058 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 77681756927) ^ 13894 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_96660055483 : Nat.Prime 96660055483 := by
  apply lucas_primality 96660055483 (2 : ZMod 96660055483)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30931, 1), (520837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30931, 1), (520837, 1)] : List FactorBlock).map factorBlockValue).prod) = 96660055483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_30931
      · exact prime_fiftyTwoAX_520837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96660055483) ^ 48330027741 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 96660055483) ^ 32220018494 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 96660055483) ^ 3125022 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 96660055483) ^ 185586 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_104287768063 : Nat.Prime 104287768063 := by
  apply lucas_primality 104287768063 (3 : ZMod 104287768063)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (37, 1), (61, 1), (409, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (37, 1), (61, 1), (409, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) = 104287768063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_409
      · exact prime_fiftyTwoAX_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104287768063) ^ 52143884031 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 34762589354 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 5488829898 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 2818588326 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 1709635542 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 254982318 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104287768063) ^ 105234882 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_104941231333 : Nat.Prime 104941231333 := by
  apply lucas_primality 104941231333 (2 : ZMod 104941231333)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) = 104941231333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_311
      · exact prime_fiftyTwoAX_85469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104941231333) ^ 52470615666 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 34980410444 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 14991604476 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 2232792156 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 337431612 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 1227828 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_104999404039 : Nat.Prime 104999404039 := by
  apply lucas_primality 104999404039 (3 : ZMod 104999404039)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17499900673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17499900673, 1)] : List FactorBlock).map factorBlockValue).prod) = 104999404039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_17499900673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104999404039) ^ 52499702019 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104999404039) ^ 34999801346 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104999404039) ^ 6 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_112073585669 : Nat.Prime 112073585669 := by
  apply lucas_primality 112073585669 (2 : ZMod 112073585669)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (53, 1), (2529421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (53, 1), (2529421, 1)] : List FactorBlock).map factorBlockValue).prod) = 112073585669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_2529421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112073585669) ^ 56036792834 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112073585669) ^ 10188507788 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112073585669) ^ 5898609772 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112073585669) ^ 2114595956 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 112073585669) ^ 44308 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_115508623117 : Nat.Prime 115508623117 := by
  apply lucas_primality 115508623117 (2 : ZMod 115508623117)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9625718593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9625718593, 1)] : List FactorBlock).map factorBlockValue).prod) = 115508623117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_9625718593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115508623117) ^ 57754311558 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 115508623117) ^ 38502874372 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 115508623117) ^ 12 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_118947318383 : Nat.Prime 118947318383 := by
  apply lucas_primality 118947318383 (10 : ZMod 118947318383)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (199, 1), (199109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (199, 1), (199109, 1)] : List FactorBlock).map factorBlockValue).prod) = 118947318383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_79
      · exact prime_fiftyTwoAX_199
      · exact prime_fiftyTwoAX_199109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 118947318383) ^ 59473659191 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 6260385178 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 1505662258 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 597725218 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 597398 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_148707154049 : Nat.Prime 148707154049 := by
  apply lucas_primality 148707154049 (3 : ZMod 148707154049)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (1161774641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (1161774641, 1)] : List FactorBlock).map factorBlockValue).prod) = 148707154049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_1161774641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 148707154049) ^ 74353577024 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 148707154049) ^ 128 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_157775415859 : Nat.Prime 157775415859 := by
  apply lucas_primality 157775415859 (2 : ZMod 157775415859)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8765300881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8765300881, 1)] : List FactorBlock).map factorBlockValue).prod) = 157775415859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_8765300881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 157775415859) ^ 78887707929 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 157775415859) ^ 52591805286 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 157775415859) ^ 18 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_201027710683 : Nat.Prime 201027710683 := by
  apply lucas_primality 201027710683 (3 : ZMod 201027710683)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (719, 1), (5177657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (719, 1), (5177657, 1)] : List FactorBlock).map factorBlockValue).prod) = 201027710683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_719
      · exact prime_fiftyTwoAX_5177657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 201027710683) ^ 100513855341 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 201027710683) ^ 67009236894 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 201027710683) ^ 279593478 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 201027710683) ^ 38826 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_202208629297 : Nat.Prime 202208629297 := by
  apply lucas_primality 202208629297 (5 : ZMod 202208629297)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (211, 1), (19965307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (211, 1), (19965307, 1)] : List FactorBlock).map factorBlockValue).prod) = 202208629297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_211
      · exact prime_fiftyTwoAX_19965307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 202208629297) ^ 101104314648 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 202208629297) ^ 67402876432 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 202208629297) ^ 958334736 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 202208629297) ^ 10128 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_204509325871 : Nat.Prime 204509325871 := by
  apply lucas_primality 204509325871 (13 : ZMod 204509325871)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (119596097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (119596097, 1)] : List FactorBlock).map factorBlockValue).prod) = 204509325871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_119596097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 204509325871) ^ 102254662935 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 204509325871) ^ 68169775290 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 204509325871) ^ 40901865174 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 204509325871) ^ 10763648730 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 204509325871) ^ 1710 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_212140652989 : Nat.Prime 212140652989 := by
  apply lucas_primality 212140652989 (2 : ZMod 212140652989)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) = 212140652989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_39198199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212140652989) ^ 106070326494 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 70713550996 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 19285513908 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5174162268 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5412 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_213502379527 : Nat.Prime 213502379527 := by
  apply lucas_primality 213502379527 (3 : ZMod 213502379527)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) = 213502379527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_1317915923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213502379527) ^ 106751189763 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 71167459842 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 162 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_297414308099 : Nat.Prime 297414308099 := by
  apply lucas_primality 297414308099 (2 : ZMod 297414308099)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (148707154049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (148707154049, 1)] : List FactorBlock).map factorBlockValue).prod) = 297414308099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_148707154049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 297414308099) ^ 148707154049 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 297414308099) ^ 2 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_299647270477 : Nat.Prime 299647270477 := by
  apply lucas_primality 299647270477 (2 : ZMod 299647270477)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (15101, 1), (32423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (15101, 1), (32423, 1)] : List FactorBlock).map factorBlockValue).prod) = 299647270477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_15101
      · exact prime_fiftyTwoAX_32423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 299647270477) ^ 149823635238 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 99882423492 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 17626310028 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 19842876 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 9241812 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_318960960511 : Nat.Prime 318960960511 := by
  apply lucas_primality 318960960511 (17 : ZMod 318960960511)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) = 318960960511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_9719
      · exact prime_fiftyTwoAX_1093943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 318960960511) ^ 159480480255 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 106320320170 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 63792192102 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 32818290 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 291570 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_359479905341 : Nat.Prime 359479905341 := by
  apply lucas_primality 359479905341 (3 : ZMod 359479905341)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (311, 1), (503, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (311, 1), (503, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) = 359479905341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_89
      · exact prime_fiftyTwoAX_311
      · exact prime_fiftyTwoAX_503
      · exact prime_fiftyTwoAX_1291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 359479905341) ^ 179739952670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 71895981068 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 4039100060 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 1155883940 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 714671780 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 278450740 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_375380267527 : Nat.Prime 375380267527 := by
  apply lucas_primality 375380267527 (5 : ZMod 375380267527)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) = 375380267527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_127
      · exact prime_fiftyTwoAX_157
      · exact prime_fiftyTwoAX_95083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 375380267527) ^ 187690133763 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 125126755842 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 34125478866 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2955750138 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2390957118 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 3947922 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_594594627721 : Nat.Prime 594594627721 := by
  apply lucas_primality 594594627721 (7 : ZMod 594594627721)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (43, 1), (115231517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (43, 1), (115231517, 1)] : List FactorBlock).map factorBlockValue).prod) = 594594627721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_115231517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 594594627721) ^ 297297313860 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 594594627721) ^ 198198209240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 594594627721) ^ 118918925544 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 594594627721) ^ 13827782040 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 594594627721) ^ 5160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_738647515831 : Nat.Prime 738647515831 := by
  apply lucas_primality 738647515831 (3 : ZMod 738647515831)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (3919, 1), (897517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (3919, 1), (897517, 1)] : List FactorBlock).map factorBlockValue).prod) = 738647515831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_3919
      · exact prime_fiftyTwoAX_897517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 738647515831) ^ 369323757915 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 246215838610 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 147729503166 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 105521073690 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 188478570 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 822990 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_906007626637 : Nat.Prime 906007626637 := by
  apply lucas_primality 906007626637 (2 : ZMod 906007626637)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) = 906007626637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_220118471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906007626637) ^ 453003813318 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 302002542212 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 129429660948 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 4116 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1066232074903 : Nat.Prime 1066232074903 := by
  apply lucas_primality 1066232074903 (5 : ZMod 1066232074903)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2111, 1), (2251, 1), (37397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2111, 1), (2251, 1), (37397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1066232074903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_2111
      · exact prime_fiftyTwoAX_2251
      · exact prime_fiftyTwoAX_37397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1066232074903) ^ 533116037451 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1066232074903) ^ 355410691634 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1066232074903) ^ 505083882 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1066232074903) ^ 473670402 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1066232074903) ^ 28511166 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1171141550269 : Nat.Prime 1171141550269 := by
  apply lucas_primality 1171141550269 (2 : ZMod 1171141550269)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (421, 1), (907, 1), (255587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (421, 1), (907, 1), (255587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171141550269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_421
      · exact prime_fiftyTwoAX_907
      · exact prime_fiftyTwoAX_255587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1171141550269) ^ 585570775134 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1171141550269) ^ 390380516756 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1171141550269) ^ 2781808908 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1171141550269) ^ 1291225524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1171141550269) ^ 4582164 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1324788685877 : Nat.Prime 1324788685877 := by
  apply lucas_primality 1324788685877 (2 : ZMod 1324788685877)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (563, 1), (34604239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (563, 1), (34604239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1324788685877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_563
      · exact prime_fiftyTwoAX_34604239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1324788685877) ^ 662394342938 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324788685877) ^ 77928746228 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324788685877) ^ 2353088252 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324788685877) ^ 38284 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_35279
      · exact prime_fiftyTwoAX_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1624159326689 : Nat.Prime 1624159326689 := by
  apply lucas_primality 1624159326689 (3 : ZMod 1624159326689)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (50754978959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (50754978959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1624159326689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_50754978959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1624159326689) ^ 812079663344 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1624159326689) ^ 32 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1874574764411 : Nat.Prime 1874574764411 := by
  apply lucas_primality 1874574764411 (2 : ZMod 1874574764411)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (733, 1), (1069, 1), (239233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (733, 1), (1069, 1), (239233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1874574764411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_733
      · exact prime_fiftyTwoAX_1069
      · exact prime_fiftyTwoAX_239233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1874574764411) ^ 937287382205 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1874574764411) ^ 374914952882 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1874574764411) ^ 2557400770 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1874574764411) ^ 1753577890 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1874574764411) ^ 7835770 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1903276866263 : Nat.Prime 1903276866263 := by
  apply lucas_primality 1903276866263 (5 : ZMod 1903276866263)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (23210693491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (23210693491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1903276866263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_23210693491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1903276866263) ^ 951638433131 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903276866263) ^ 46421386982 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903276866263) ^ 82 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2097817565491 : Nat.Prime 2097817565491 := by
  apply lucas_primality 2097817565491 (17 : ZMod 2097817565491)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (103, 1), (991, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (103, 1), (991, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2097817565491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_103
      · exact prime_fiftyTwoAX_991
      · exact prime_fiftyTwoAX_25373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2097817565491) ^ 1048908782745 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 699272521830 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 419563513098 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 20367160830 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 2116869390 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 82679130 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_3088871442451 : Nat.Prime 3088871442451 := by
  apply lucas_primality 3088871442451 (2 : ZMod 3088871442451)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (6864158761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (6864158761, 1)] : List FactorBlock).map factorBlockValue).prod) = 3088871442451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_6864158761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3088871442451) ^ 1544435721225 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3088871442451) ^ 1029623814150 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3088871442451) ^ 617774288490 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3088871442451) ^ 450 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_5000095063219 : Nat.Prime 5000095063219 := by
  apply lucas_primality 5000095063219 (2 : ZMod 5000095063219)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (642871, 1), (1296293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (642871, 1), (1296293, 1)] : List FactorBlock).map factorBlockValue).prod) = 5000095063219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_642871
      · exact prime_fiftyTwoAX_1296293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5000095063219) ^ 2500047531609 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 1666698354406 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 7777758 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 3857226 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_5452977238001 : Nat.Prime 5452977238001 := by
  apply lucas_primality 5452977238001 (3 : ZMod 5452977238001)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) = 5452977238001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_3877
      · exact prime_fiftyTwoAX_37013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5452977238001) ^ 2726488619000 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1090595447600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 286998802000 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1406494000 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 147326000 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_7070795998229 : Nat.Prime 7070795998229 := by
  apply lucas_primality 7070795998229 (2 : ZMod 7070795998229)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (4211, 1), (1125419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (4211, 1), (1125419, 1)] : List FactorBlock).map factorBlockValue).prod) = 7070795998229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_373
      · exact prime_fiftyTwoAX_4211
      · exact prime_fiftyTwoAX_1125419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7070795998229) ^ 3535397999114 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 18956557636 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 1679125148 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 6282812 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_7561731942337 : Nat.Prime 7561731942337 := by
  apply lucas_primality 7561731942337 (10 : ZMod 7561731942337)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 2), (13, 1), (25037521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 2), (13, 1), (25037521, 1)] : List FactorBlock).map factorBlockValue).prod) = 7561731942337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_25037521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7561731942337) ^ 3780865971168 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 7561731942337) ^ 2520577314112 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 7561731942337) ^ 687430176576 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 7561731942337) ^ 581671687872 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 7561731942337) ^ 302016 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_9755571039311 : Nat.Prime 9755571039311 := by
  apply lucas_primality 9755571039311 (13 : ZMod 9755571039311)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (389, 1), (1663, 1), (1508033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (389, 1), (1663, 1), (1508033, 1)] : List FactorBlock).map factorBlockValue).prod) = 9755571039311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_389
      · exact prime_fiftyTwoAX_1663
      · exact prime_fiftyTwoAX_1508033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9755571039311) ^ 4877785519655 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9755571039311) ^ 1951114207862 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9755571039311) ^ 25078588790 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9755571039311) ^ 5866248370 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9755571039311) ^ 6469070 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_12291142418257 : Nat.Prime 12291142418257 := by
  apply lucas_primality 12291142418257 (5 : ZMod 12291142418257)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (83, 1), (237317393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (83, 1), (237317393, 1)] : List FactorBlock).map factorBlockValue).prod) = 12291142418257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_237317393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12291142418257) ^ 6145571209128 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 4097047472752 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 945472493712 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 148086053232 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 51792 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_17031952951339 : Nat.Prime 17031952951339 := by
  apply lucas_primality 17031952951339 (10 : ZMod 17031952951339)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (41, 1), (101, 1), (1301, 1), (40531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (41, 1), (101, 1), (1301, 1), (40531, 1)] : List FactorBlock).map factorBlockValue).prod) = 17031952951339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_101
      · exact prime_fiftyTwoAX_1301
      · exact prime_fiftyTwoAX_40531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 17031952951339) ^ 8515976475669 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 5677317650446 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 1310150227026 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 415413486618 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 168633197538 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 13091431938 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17031952951339) ^ 420220398 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_18349824068501 : Nat.Prime 18349824068501 := by
  apply lucas_primality 18349824068501 (2 : ZMod 18349824068501)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (36699648137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (36699648137, 1)] : List FactorBlock).map factorBlockValue).prod) = 18349824068501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_36699648137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18349824068501) ^ 9174912034250 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18349824068501) ^ 3669964813700 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18349824068501) ^ 500 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_18414098321657 : Nat.Prime 18414098321657 := by
  apply lucas_primality 18414098321657 (3 : ZMod 18414098321657)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (1973, 1), (19773401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (1973, 1), (19773401, 1)] : List FactorBlock).map factorBlockValue).prod) = 18414098321657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_1973
      · exact prime_fiftyTwoAX_19773401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18414098321657) ^ 9207049160828 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18414098321657) ^ 312103361384 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18414098321657) ^ 9333045272 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 18414098321657) ^ 931256 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_24705200084659 : Nat.Prime 24705200084659 := by
  apply lucas_primality 24705200084659 (2 : ZMod 24705200084659)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) = 24705200084659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_229
      · exact prime_fiftyTwoAX_12569
      · exact prime_fiftyTwoAX_1430543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24705200084659) ^ 12352600042329 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 8235066694886 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 107882969802 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 1965566082 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 17269806 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_26766338248187 : Nat.Prime 26766338248187 := by
  apply lucas_primality 26766338248187 (2 : ZMod 26766338248187)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (576523, 1), (23213591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (576523, 1), (23213591, 1)] : List FactorBlock).map factorBlockValue).prod) = 26766338248187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_576523
      · exact prime_fiftyTwoAX_23213591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26766338248187) ^ 13383169124093 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26766338248187) ^ 46427182 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26766338248187) ^ 1153046 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_28322570842457 : Nat.Prime 28322570842457 := by
  apply lucas_primality 28322570842457 (5 : ZMod 28322570842457)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28322570842457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_5569
      · exact prime_fiftyTwoAX_3399569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28322570842457) ^ 14161285421228 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 2574779167496 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 1666033578968 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 5085755224 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 8331224 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_50456514775123 : Nat.Prime 50456514775123 := by
  apply lucas_primality 50456514775123 (2 : ZMod 50456514775123)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) = 50456514775123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_2593
      · exact prime_fiftyTwoAX_360347051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50456514775123) ^ 25228257387561 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 16818838258374 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 19458740754 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 140022 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_52444761318179 : Nat.Prime 52444761318179 := by
  apply lucas_primality 52444761318179 (2 : ZMod 52444761318179)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (497677, 1), (52689557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (497677, 1), (52689557, 1)] : List FactorBlock).map factorBlockValue).prod) = 52444761318179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_497677
      · exact prime_fiftyTwoAX_52689557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52444761318179) ^ 26222380659089 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52444761318179) ^ 105379114 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 52444761318179) ^ 995354 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_89
      · exact prime_fiftyTwoAX_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_102102247358591 : Nat.Prime 102102247358591 := by
  apply lucas_primality 102102247358591 (14 : ZMod 102102247358591)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) = 102102247358591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_523
      · exact prime_fiftyTwoAX_10159
      · exact prime_fiftyTwoAX_1921687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 102102247358591) ^ 51051123679295 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 20420449471718 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 195224182330 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 10050423010 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 53131570 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_104889522636359 : Nat.Prime 104889522636359 := by
  apply lucas_primality 104889522636359 (13 : ZMod 104889522636359)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52444761318179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52444761318179, 1)] : List FactorBlock).map factorBlockValue).prod) = 104889522636359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_52444761318179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 104889522636359) ^ 52444761318179 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 104889522636359) ^ 2 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_118827294373519 : Nat.Prime 118827294373519 := by
  apply lucas_primality 118827294373519 (6 : ZMod 118827294373519)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (80833, 1), (415969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (80833, 1), (415969, 1)] : List FactorBlock).map factorBlockValue).prod) = 118827294373519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_80833
      · exact prime_fiftyTwoAX_415969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118827294373519) ^ 59413647186759 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118827294373519) ^ 39609098124506 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118827294373519) ^ 6254068124922 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118827294373519) ^ 3833138528178 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118827294373519) ^ 1470034446 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118827294373519) ^ 285663822 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_119134327776067 : Nat.Prime 119134327776067 := by
  apply lucas_primality 119134327776067 (7 : ZMod 119134327776067)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119134327776067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_213502379527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119134327776067) ^ 59567163888033 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 39711442592022 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 3843042831486 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 558 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_120139508808577 : Nat.Prime 120139508808577 := by
  apply lucas_primality 120139508808577 (5 : ZMod 120139508808577)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (104287768063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (104287768063, 1)] : List FactorBlock).map factorBlockValue).prod) = 120139508808577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_104287768063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 120139508808577) ^ 60069754404288 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 120139508808577) ^ 40046502936192 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 120139508808577) ^ 1152 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_160284903568781 : Nat.Prime 160284903568781 := by
  apply lucas_primality 160284903568781 (2 : ZMod 160284903568781)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) = 160284903568781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_113
      · exact prime_fiftyTwoAX_68392019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160284903568781) ^ 80142451784390 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 32056980713756 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 9428523739340 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2627621369980 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 1418450474060 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2343620 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_170319529513391 : Nat.Prime 170319529513391 := by
  apply lucas_primality 170319529513391 (13 : ZMod 170319529513391)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17031952951339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17031952951339, 1)] : List FactorBlock).map factorBlockValue).prod) = 170319529513391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_17031952951339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 170319529513391) ^ 85159764756695 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 170319529513391) ^ 34063905902678 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (13 : ZMod 170319529513391) ^ 10 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_226043412291283 : Nat.Prime 226043412291283 := by
  apply lucas_primality 226043412291283 (2 : ZMod 226043412291283)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) = 226043412291283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_359
      · exact prime_fiftyTwoAX_104941231333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226043412291283) ^ 113021706145641 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 75347804097094 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 629647387998 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 2154 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_346169717796127 : Nat.Prime 346169717796127 := by
  apply lucas_primality 346169717796127 (3 : ZMod 346169717796127)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (201027710683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (201027710683, 1)] : List FactorBlock).map factorBlockValue).prod) = 346169717796127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_201027710683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 346169717796127) ^ 173084858898063 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 346169717796127) ^ 115389905932042 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 346169717796127) ^ 49452816828018 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 346169717796127) ^ 8443163848686 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 346169717796127) ^ 1722 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_358964277063341 : Nat.Prime 358964277063341 := by
  apply lucas_primality 358964277063341 (2 : ZMod 358964277063341)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (123427, 1), (11185817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (123427, 1), (11185817, 1)] : List FactorBlock).map factorBlockValue).prod) = 358964277063341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_123427
      · exact prime_fiftyTwoAX_11185817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 358964277063341) ^ 179482138531670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 358964277063341) ^ 71792855412668 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 358964277063341) ^ 27612636697180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 358964277063341) ^ 2908312420 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 358964277063341) ^ 32091020 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_366444555641737 : Nat.Prime 366444555641737 := by
  apply lucas_primality 366444555641737 (5 : ZMod 366444555641737)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) = 366444555641737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_487
      · exact prime_fiftyTwoAX_1381
      · exact prime_fiftyTwoAX_158759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 366444555641737) ^ 183222277820868 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 122148185213912 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 33313141421976 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 28188042741672 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 752452886328 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 265347252456 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 2308181304 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_375886089384859 : Nat.Prime 375886089384859 := by
  apply lucas_primality 375886089384859 (7 : ZMod 375886089384859)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (278911, 1), (1919789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (278911, 1), (1919789, 1)] : List FactorBlock).map factorBlockValue).prod) = 375886089384859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_278911
      · exact prime_fiftyTwoAX_1919789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 375886089384859) ^ 187943044692429 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 125295363128286 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 28914314568066 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 1347691878 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 195795522 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_425248261460767 : Nat.Prime 425248261460767 := by
  apply lucas_primality 425248261460767 (5 : ZMod 425248261460767)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (227, 1), (541, 1), (599, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (227, 1), (541, 1), (599, 1), (107053, 1)] : List FactorBlock).map factorBlockValue).prod) = 425248261460767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_227
      · exact prime_fiftyTwoAX_541
      · exact prime_fiftyTwoAX_599
      · exact prime_fiftyTwoAX_107053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 425248261460767) ^ 212624130730383 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 425248261460767) ^ 141749420486922 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 425248261460767) ^ 1873340358858 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 425248261460767) ^ 786041148726 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 425248261460767) ^ 709930319634 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 425248261460767) ^ 3972315222 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_581810508705311 : Nat.Prime 581810508705311 := by
  apply lucas_primality 581810508705311 (7 : ZMod 581810508705311)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (995117, 1), (1243969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (995117, 1), (1243969, 1)] : List FactorBlock).map factorBlockValue).prod) = 581810508705311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_995117
      · exact prime_fiftyTwoAX_1243969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 581810508705311) ^ 290905254352655 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 116362101741062 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 12378946993730 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 584665430 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 467704990 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_585686675729543 : Nat.Prime 585686675729543 := by
  apply lucas_primality 585686675729543 (5 : ZMod 585686675729543)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2789, 1), (104999404039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2789, 1), (104999404039, 1)] : List FactorBlock).map factorBlockValue).prod) = 585686675729543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_2789
      · exact prime_fiftyTwoAX_104999404039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 585686675729543) ^ 292843337864771 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 585686675729543) ^ 209998808078 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 585686675729543) ^ 5578 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_971029727964899 : Nat.Prime 971029727964899 := by
  apply lucas_primality 971029727964899 (2 : ZMod 971029727964899)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (1874574764411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (1874574764411, 1)] : List FactorBlock).map factorBlockValue).prod) = 971029727964899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_1874574764411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 971029727964899) ^ 485514863982449 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 971029727964899) ^ 138718532566414 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 971029727964899) ^ 26244046701754 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 971029727964899) ^ 518 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_985288906104631 : Nat.Prime 985288906104631 := by
  apply lucas_primality 985288906104631 (3 : ZMod 985288906104631)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157, 1), (5647, 1), (37044599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157, 1), (5647, 1), (37044599, 1)] : List FactorBlock).map factorBlockValue).prod) = 985288906104631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_157
      · exact prime_fiftyTwoAX_5647
      · exact prime_fiftyTwoAX_37044599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 985288906104631) ^ 492644453052315 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 985288906104631) ^ 328429635368210 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 985288906104631) ^ 197057781220926 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 985288906104631) ^ 6275725516590 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 985288906104631) ^ 174480061290 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 985288906104631) ^ 26597370 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1091318243936369 : Nat.Prime 1091318243936369 := by
  apply lucas_primality 1091318243936369 (3 : ZMod 1091318243936369)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091318243936369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_5327453741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1091318243936369) ^ 545659121968184 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 155902606276624 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 35203814320528 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 18496919388752 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 204848 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1422011291666261 : Nat.Prime 1422011291666261 := by
  apply lucas_primality 1422011291666261 (2 : ZMod 1422011291666261)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6247, 1), (11381553479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6247, 1), (11381553479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1422011291666261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_6247
      · exact prime_fiftyTwoAX_11381553479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1422011291666261) ^ 711005645833130 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1422011291666261) ^ 284402258333252 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1422011291666261) ^ 227631069580 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1422011291666261) ^ 124940 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1573359879384229 : Nat.Prime 1573359879384229 := by
  apply lucas_primality 1573359879384229 (7 : ZMod 1573359879384229)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (277, 1), (110947, 1), (328177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (277, 1), (110947, 1), (328177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1573359879384229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_277
      · exact prime_fiftyTwoAX_110947
      · exact prime_fiftyTwoAX_328177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1573359879384229) ^ 786679939692114 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1573359879384229) ^ 524453293128076 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1573359879384229) ^ 121027683029556 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1573359879384229) ^ 5679999564564 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1573359879384229) ^ 14181184524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1573359879384229) ^ 4794241764 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2471108671067591 : Nat.Prime 2471108671067591 := by
  apply lucas_primality 2471108671067591 (11 : ZMod 2471108671067591)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211, 1), (1171141550269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211, 1), (1171141550269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2471108671067591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_211
      · exact prime_fiftyTwoAX_1171141550269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2471108671067591) ^ 1235554335533795 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 2471108671067591) ^ 494221734213518 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 2471108671067591) ^ 11711415502690 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 2471108671067591) ^ 2110 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_3080389673224709 : Nat.Prime 3080389673224709 := by
  apply lucas_primality 3080389673224709 (2 : ZMod 3080389673224709)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3080389673224709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_967
      · exact prime_fiftyTwoAX_28229
      · exact prime_fiftyTwoAX_166931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3080389673224709) ^ 1540194836612354 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 236953051786516 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 3185511554524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 109121459252 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 18453071468 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_5001259242180419 : Nat.Prime 5001259242180419 := by
  apply lucas_primality 5001259242180419 (2 : ZMod 5001259242180419)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (1009, 1), (2311, 1), (1939247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (1009, 1), (2311, 1), (1939247, 1)] : List FactorBlock).map factorBlockValue).prod) = 5001259242180419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_79
      · exact prime_fiftyTwoAX_1009
      · exact prime_fiftyTwoAX_2311
      · exact prime_fiftyTwoAX_1939247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5001259242180419) ^ 2500629621090209 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5001259242180419) ^ 714465606025774 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5001259242180419) ^ 63307079014942 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5001259242180419) ^ 4956649397602 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5001259242180419) ^ 2164110446638 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5001259242180419) ^ 2578969694 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_7288069400372093 : Nat.Prime 7288069400372093 := by
  apply lucas_primality 7288069400372093 (2 : ZMod 7288069400372093)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (1087, 1), (104161, 1), (193883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (1087, 1), (104161, 1), (193883, 1)] : List FactorBlock).map factorBlockValue).prod) = 7288069400372093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_1087
      · exact prime_fiftyTwoAX_104161
      · exact prime_fiftyTwoAX_193883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7288069400372093) ^ 3644034700186046 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7288069400372093) ^ 87808065064724 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7288069400372093) ^ 6704755658116 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7288069400372093) ^ 69969272572 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7288069400372093) ^ 37590038324 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_11895479753831941 : Nat.Prime 11895479753831941 := by
  apply lucas_primality 11895479753831941 (2 : ZMod 11895479753831941)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11895479753831941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_28322570842457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11895479753831941) ^ 5947739876915970 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 3965159917943980 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 2379095950766388 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 1699354250547420 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 420 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_18843021286721663 : Nat.Prime 18843021286721663 := by
  apply lucas_primality 18843021286721663 (5 : ZMod 18843021286721663)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26669, 1), (274831, 1), (1285429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26669, 1), (274831, 1), (1285429, 1)] : List FactorBlock).map factorBlockValue).prod) = 18843021286721663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_26669
      · exact prime_fiftyTwoAX_274831
      · exact prime_fiftyTwoAX_1285429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18843021286721663) ^ 9421510643360831 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 706551474998 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 68562212002 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 14658935878 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_384973
      · exact prime_fiftyTwoAX_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_25024350819790243 : Nat.Prime 25024350819790243 := by
  apply lucas_primality 25024350819790243 (2 : ZMod 25024350819790243)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) = 25024350819790243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_47149
      · exact prime_fiftyTwoAX_29486133581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25024350819790243) ^ 12512175409895121 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 8341450273263414 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 530750404458 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 848682 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_30133561870930829 : Nat.Prime 30133561870930829 := by
  apply lucas_primality 30133561870930829 (2 : ZMod 30133561870930829)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) = 30133561870930829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_160284903568781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30133561870930829) ^ 15066780935465414 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 641139614275124 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 188 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_37257918005830523 : Nat.Prime 37257918005830523 := by
  apply lucas_primality 37257918005830523 (5 : ZMod 37257918005830523)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (13, 2), (204509325871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (13, 2), (204509325871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37257918005830523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_204509325871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37257918005830523) ^ 18628959002915261 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37257918005830523) ^ 5322559715118646 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37257918005830523) ^ 3387083455075502 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37257918005830523) ^ 2865993692756194 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37257918005830523) ^ 182182 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_50467968185178619 : Nat.Prime 50467968185178619 := by
  apply lucas_primality 50467968185178619 (2 : ZMod 50467968185178619)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (149, 1), (271, 1), (1049, 1), (1051, 1), (62981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (149, 1), (271, 1), (1049, 1), (1051, 1), (62981, 1)] : List FactorBlock).map factorBlockValue).prod) = 50467968185178619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_149
      · exact prime_fiftyTwoAX_271
      · exact prime_fiftyTwoAX_1049
      · exact prime_fiftyTwoAX_1051
      · exact prime_fiftyTwoAX_62981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50467968185178619) ^ 25233984092589309 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 16822656061726206 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 338711195873682 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 186228664889958 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 48110551177482 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 48018999224718 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 801320528178 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_59620468873578253 : Nat.Prime 59620468873578253 := by
  apply lucas_primality 59620468873578253 (2 : ZMod 59620468873578253)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43013, 1), (115508623117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43013, 1), (115508623117, 1)] : List FactorBlock).map factorBlockValue).prod) = 59620468873578253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_43013
      · exact prime_fiftyTwoAX_115508623117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59620468873578253) ^ 29810234436789126 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59620468873578253) ^ 19873489624526084 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59620468873578253) ^ 1386103477404 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59620468873578253) ^ 516156 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_76967870515442089 : Nat.Prime 76967870515442089 := by
  apply lucas_primality 76967870515442089 (11 : ZMod 76967870515442089)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (59, 1), (61, 1), (9792080843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (59, 1), (61, 1), (9792080843, 1)] : List FactorBlock).map factorBlockValue).prod) = 76967870515442089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_9792080843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 76967870515442089) ^ 38483935257721044 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 25655956838480696 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 10995410073634584 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 5920605424264776 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 1304540178227832 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 1261768369105608 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (11 : ZMod 76967870515442089) ^ 7860216 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_171663126899945669 : Nat.Prime 171663126899945669 := by
  apply lucas_primality 171663126899945669 (2 : ZMod 171663126899945669)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (479, 1), (299647270477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (479, 1), (299647270477, 1)] : List FactorBlock).map factorBlockValue).prod) = 171663126899945669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_479
      · exact prime_fiftyTwoAX_299647270477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171663126899945669) ^ 85831563449972834 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 13204855915380436 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 7463614213041116 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 358378135490492 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 572884 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_239766403692867703 : Nat.Prime 239766403692867703 := by
  apply lucas_primality 239766403692867703 (3 : ZMod 239766403692867703)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) = 239766403692867703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_89
      · exact prime_fiftyTwoAX_1753
      · exact prime_fiftyTwoAX_16097
      · exact prime_fiftyTwoAX_2273119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239766403692867703) ^ 119883201846433851 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 79922134564289234 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 34252343384695386 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 2694004535874918 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 136774902277734 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 14895098694966 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 105479037258 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_426950491054489151 : Nat.Prime 426950491054489151 := by
  apply lucas_primality 426950491054489151 (7 : ZMod 426950491054489151)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) = 426950491054489151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_2767
      · exact prime_fiftyTwoAX_19167809209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 426950491054489151) ^ 213475245527244575 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 85390098210897830 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 60992927293498450 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 18563064828456050 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 154300864132450 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 22274350 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_61717
      · exact prime_fiftyTwoAX_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1603952514074243401 : Nat.Prime 1603952514074243401 := by
  apply lucas_primality 1603952514074243401 (7 : ZMod 1603952514074243401)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603952514074243401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_67819
      · exact prime_fiftyTwoAX_2596501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603952514074243401) ^ 801976257037121700 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 534650838024747800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 320790502814848680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 94350147886720200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 84418553372328600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 34126649235622200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 23650489008600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 617736143400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2009831726809906421 : Nat.Prime 2009831726809906421 := by
  apply lucas_primality 2009831726809906421 (2 : ZMod 2009831726809906421)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009831726809906421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_557
      · exact prime_fiftyTwoAX_409901
      · exact prime_fiftyTwoAX_440144753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2009831726809906421) ^ 1004915863404953210 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 401966345361981284 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 3608315487989060 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4903212548420 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4566297140 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_4701987520742701253 : Nat.Prime 4701987520742701253 := by
  apply lucas_primality 4701987520742701253 (2 : ZMod 4701987520742701253)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1601, 1), (104889522636359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1601, 1), (104889522636359, 1)] : List FactorBlock).map factorBlockValue).prod) = 4701987520742701253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_1601
      · exact prime_fiftyTwoAX_104889522636359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4701987520742701253) ^ 2350993760371350626 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701987520742701253) ^ 671712502963243036 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701987520742701253) ^ 2936906633818052 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701987520742701253) ^ 44828 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_6276586759550679409 : Nat.Prime 6276586759550679409 := by
  apply lucas_primality 6276586759550679409 (7 : ZMod 6276586759550679409)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) = 6276586759550679409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_254927
      · exact prime_fiftyTwoAX_11928834361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6276586759550679409) ^ 3138293379775339704 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 2092195586516893136 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 145967133943039056 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 24621114121104 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 526169328 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_7777367187437459221 : Nat.Prime 7777367187437459221 := by
  apply lucas_primality 7777367187437459221 (6 : ZMod 7777367187437459221)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7777367187437459221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_367
      · exact prime_fiftyTwoAX_50456514775123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7777367187437459221) ^ 3888683593718729610 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 2592455729145819740 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1555473437487491844 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1111052455348208460 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 21191736205551660 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 154140 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_439
      · exact prime_fiftyTwoAX_853
      · exact prime_fiftyTwoAX_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_13145780685211854149 : Nat.Prime 13145780685211854149 := by
  apply lucas_primality 13145780685211854149 (2 : ZMod 13145780685211854149)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) = 13145780685211854149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_67
      · exact prime_fiftyTwoAX_226043412291283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13145780685211854149) ^ 6572890342605927074 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 1877968669315979164 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 424057441458446908 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 196205681868833644 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 58156 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_18882334233565692523 : Nat.Prime 18882334233565692523 := by
  apply lucas_primality 18882334233565692523 (2 : ZMod 18882334233565692523)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1500157, 1), (2097817565491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1500157, 1), (2097817565491, 1)] : List FactorBlock).map factorBlockValue).prod) = 18882334233565692523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_1500157
      · exact prime_fiftyTwoAX_2097817565491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18882334233565692523) ^ 9441167116782846261 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 6294111411188564174 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 12586905392946 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 9000942 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_25972933670031552247 : Nat.Prime 25972933670031552247 := by
  apply lucas_primality 25972933670031552247 (3 : ZMod 25972933670031552247)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 2), (17, 1), (3251, 1), (6113, 1), (3228259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 2), (17, 1), (3251, 1), (6113, 1), (3228259, 1)] : List FactorBlock).map factorBlockValue).prod) = 25972933670031552247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_3251
      · exact prime_fiftyTwoAX_6113
      · exact prime_fiftyTwoAX_3228259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25972933670031552247) ^ 12986466835015776123 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 8657644556677184082 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 3710419095718793178 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 1527819627648914838 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 7989213678877746 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 4248803152303542 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25972933670031552247) ^ 8045492530194 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_54435041108956384361 : Nat.Prime 54435041108956384361 := by
  apply lucas_primality 54435041108956384361 (6 : ZMod 54435041108956384361)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (243182789, 1), (508736671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (243182789, 1), (508736671, 1)] : List FactorBlock).map factorBlockValue).prod) = 54435041108956384361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_243182789
      · exact prime_fiftyTwoAX_508736671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54435041108956384361) ^ 27217520554478192180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 10887008221791276872 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 4948640100814216760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 223844135240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 107000427160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_67337590816601618489 : Nat.Prime 67337590816601618489 := by
  apply lucas_primality 67337590816601618489 (6 : ZMod 67337590816601618489)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67337590816601618489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_71
      · exact prime_fiftyTwoAX_9269333
      · exact prime_fiftyTwoAX_752335981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67337590816601618489) ^ 33668795408300809244 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 3961034753917742264 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 948416772064811528 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 7264556232536 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 89504679448 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_75529336934262770093 : Nat.Prime 75529336934262770093 := by
  apply lucas_primality 75529336934262770093 (2 : ZMod 75529336934262770093)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18882334233565692523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18882334233565692523, 1)] : List FactorBlock).map factorBlockValue).prod) = 75529336934262770093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_18882334233565692523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 75529336934262770093) ^ 37764668467131385046 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75529336934262770093) ^ 4 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_82651541869666928401 : Nat.Prime 82651541869666928401 := by
  apply lucas_primality 82651541869666928401 (14 : ZMod 82651541869666928401)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (11, 1), (23, 2), (6379, 1), (1855533307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (11, 1), (23, 2), (6379, 1), (1855533307, 1)] : List FactorBlock).map factorBlockValue).prod) = 82651541869666928401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_6379
      · exact prime_fiftyTwoAX_1855533307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 82651541869666928401) ^ 41325770934833464200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 27550513956555642800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 16530308373933385680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 7513776533606084400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 3593545298681170800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 12956817976119600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 44543281200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_95376871458287904733 : Nat.Prime 95376871458287904733 := by
  apply lucas_primality 95376871458287904733 (2 : ZMod 95376871458287904733)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (359, 1), (248371, 1), (6856826173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (359, 1), (248371, 1), (6856826173, 1)] : List FactorBlock).map factorBlockValue).prod) = 95376871458287904733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_359
      · exact prime_fiftyTwoAX_248371
      · exact prime_fiftyTwoAX_6856826173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95376871458287904733) ^ 47688435729143952366 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95376871458287904733) ^ 31792290486095968244 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95376871458287904733) ^ 7336682419868300364 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95376871458287904733) ^ 265673736652612548 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95376871458287904733) ^ 384009692992692 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95376871458287904733) ^ 13909769484 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_130004395631094960253 : Nat.Prime 130004395631094960253 := by
  apply lucas_primality 130004395631094960253 (2 : ZMod 130004395631094960253)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) = 130004395631094960253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_146173
      · exact prime_fiftyTwoAX_24705200084659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130004395631094960253) ^ 65002197815547480126 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 43334798543698320084 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 889387203047724 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 5262228 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_151452027015398879101 : Nat.Prime 151452027015398879101 := by
  apply lucas_primality 151452027015398879101 (6 : ZMod 151452027015398879101)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11202857, 1), (45063512821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11202857, 1), (45063512821, 1)] : List FactorBlock).map factorBlockValue).prod) = 151452027015398879101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_11202857
      · exact prime_fiftyTwoAX_45063512821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 151452027015398879101) ^ 75726013507699439550 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 151452027015398879101) ^ 50484009005132959700 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 151452027015398879101) ^ 30290405403079775820 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 151452027015398879101) ^ 13519053846300 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 151452027015398879101) ^ 3360857100 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_189403780999497233633 : Nat.Prime 189403780999497233633 := by
  apply lucas_primality 189403780999497233633 (3 : ZMod 189403780999497233633)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (367, 1), (361451, 1), (44619343003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (367, 1), (361451, 1), (44619343003, 1)] : List FactorBlock).map factorBlockValue).prod) = 189403780999497233633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_367
      · exact prime_fiftyTwoAX_361451
      · exact prime_fiftyTwoAX_44619343003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 189403780999497233633) ^ 94701890499748616816 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 189403780999497233633) ^ 516086596728875296 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 189403780999497233633) ^ 524009564227232 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 189403780999497233633) ^ 4244880544 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_286099355001209160109 : Nat.Prime 286099355001209160109 := by
  apply lucas_primality 286099355001209160109 (6 : ZMod 286099355001209160109)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (200438423, 1), (118947318383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (200438423, 1), (118947318383, 1)] : List FactorBlock).map factorBlockValue).prod) = 286099355001209160109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_200438423
      · exact prime_fiftyTwoAX_118947318383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 286099355001209160109) ^ 143049677500604580054 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 95366451667069720036 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 1427367820596 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 2405261076 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_344137326892735588579 : Nat.Prime 344137326892735588579 := by
  apply lucas_primality 344137326892735588579 (2 : ZMod 344137326892735588579)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (714283, 1), (26766338248187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (714283, 1), (26766338248187, 1)] : List FactorBlock).map factorBlockValue).prod) = 344137326892735588579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_714283
      · exact prime_fiftyTwoAX_26766338248187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344137326892735588579) ^ 172068663446367794289 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 114712442297578529526 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 481794088467366 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 12857094 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1043046175479247871761 : Nat.Prime 1043046175479247871761 := by
  apply lucas_primality 1043046175479247871761 (19 : ZMod 1043046175479247871761)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (61, 1), (155693, 1), (421133, 1), (1086611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (61, 1), (155693, 1), (421133, 1), (1086611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1043046175479247871761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_61
      · exact prime_fiftyTwoAX_155693
      · exact prime_fiftyTwoAX_421133
      · exact prime_fiftyTwoAX_1086611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1043046175479247871761) ^ 521523087739623935880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 347682058493082623920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 208609235095849574352 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 17099117630807342160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 6699377463850320 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 2476761914832720 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 959907616874160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2124561888099414885917 : Nat.Prime 2124561888099414885917 := by
  apply lucas_primality 2124561888099414885917 (2 : ZMod 2124561888099414885917)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2124561888099414885917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_131
      · exact prime_fiftyTwoAX_10801067
      · exact prime_fiftyTwoAX_375380267527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2124561888099414885917) ^ 1062280944049707442958 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 16218029680148205236 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 196699260184148 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 5659759108 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_107
      · exact prime_fiftyTwoAX_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_3359842904617050103151 : Nat.Prime 3359842904617050103151 := by
  apply lucas_primality 3359842904617050103151 (7 : ZMod 3359842904617050103151)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (71, 1), (383, 1), (2471108671067591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (71, 1), (383, 1), (2471108671067591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3359842904617050103151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_71
      · exact prime_fiftyTwoAX_383
      · exact prime_fiftyTwoAX_2471108671067591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3359842904617050103151) ^ 1679921452308525051575 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3359842904617050103151) ^ 671968580923410020630 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3359842904617050103151) ^ 47321731050944367650 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3359842904617050103151) ^ 8772435782289948050 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3359842904617050103151) ^ 1359650 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_3720151109024930829341 : Nat.Prime 3720151109024930829341 := by
  apply lucas_primality 3720151109024930829341 (10 : ZMod 3720151109024930829341)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720151109024930829341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_1873
      · exact prime_fiftyTwoAX_1091318243936369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3720151109024930829341) ^ 1860075554512465414670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 744030221804986165868 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 531450158432132975620 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 286165469924994679180 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 1986199203964191580 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 3408860 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_4017232481722971149851 : Nat.Prime 4017232481722971149851 := by
  apply lucas_primality 4017232481722971149851 (2 : ZMod 4017232481722971149851)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1063, 1), (1373, 1), (18349824068501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1063, 1), (1373, 1), (18349824068501, 1)] : List FactorBlock).map factorBlockValue).prod) = 4017232481722971149851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_1063
      · exact prime_fiftyTwoAX_1373
      · exact prime_fiftyTwoAX_18349824068501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4017232481722971149851) ^ 2008616240861485574925 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 1339077493907657049950 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 803446496344594229970 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 3779146266907780950 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 2925879447722484450 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 218924850 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_25116282422222531860373 : Nat.Prime 25116282422222531860373 := by
  apply lucas_primality 25116282422222531860373 (2 : ZMod 25116282422222531860373)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (103, 1), (663203, 1), (7070795998229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (103, 1), (663203, 1), (7070795998229, 1)] : List FactorBlock).map factorBlockValue).prod) = 25116282422222531860373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_103
      · exact prime_fiftyTwoAX_663203
      · exact prime_fiftyTwoAX_7070795998229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25116282422222531860373) ^ 12558141211111265930186 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 1932021724786348604644 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 243847402157500309324 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 37871183366514524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 3552115268 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_27003171696706649216161 : Nat.Prime 27003171696706649216161 := by
  apply lucas_primality 27003171696706649216161 (23 : ZMod 27003171696706649216161)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (31, 1), (83, 1), (7288069400372093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (31, 1), (83, 1), (7288069400372093, 1)] : List FactorBlock).map factorBlockValue).prod) = 27003171696706649216161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_7288069400372093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 27003171696706649216161) ^ 13501585848353324608080 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (23 : ZMod 27003171696706649216161) ^ 9001057232235549738720 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (23 : ZMod 27003171696706649216161) ^ 5400634339341329843232 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (23 : ZMod 27003171696706649216161) ^ 871070054732472555360 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (23 : ZMod 27003171696706649216161) ^ 325339418032610231520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (23 : ZMod 27003171696706649216161) ^ 3705120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_29114950708575121538557 : Nat.Prime 29114950708575121538557 := by
  apply lucas_primality 29114950708575121538557 (2 : ZMod 29114950708575121538557)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (2837, 1), (5001259242180419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (2837, 1), (5001259242180419, 1)] : List FactorBlock).map factorBlockValue).prod) = 29114950708575121538557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_2837
      · exact prime_fiftyTwoAX_5001259242180419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29114950708575121538557) ^ 14557475354287560769278 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114950708575121538557) ^ 9704983569525040512852 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114950708575121538557) ^ 1532365826767111659924 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114950708575121538557) ^ 10262583964954219788 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114950708575121538557) ^ 5821524 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_57930558174113115402061 : Nat.Prime 57930558174113115402061 := by
  apply lucas_primality 57930558174113115402061 (2 : ZMod 57930558174113115402061)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1659491, 1), (581810508705311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1659491, 1), (581810508705311, 1)] : List FactorBlock).map factorBlockValue).prod) = 57930558174113115402061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_1659491
      · exact prime_fiftyTwoAX_581810508705311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57930558174113115402061) ^ 28965279087056557701030 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 19310186058037705134020 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 11586111634822623080412 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 34908630522318660 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 99569460 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_58314049232250980939707 : Nat.Prime 58314049232250980939707 := by
  apply lucas_primality 58314049232250980939707 (2 : ZMod 58314049232250980939707)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (53, 1), (4701987520742701253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (53, 1), (4701987520742701253, 1)] : List FactorBlock).map factorBlockValue).prod) = 58314049232250980939707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_4701987520742701253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58314049232250980939707) ^ 29157024616125490469853 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58314049232250980939707) ^ 19438016410750326979902 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58314049232250980939707) ^ 4485696094788536995362 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58314049232250980939707) ^ 1100265079853792093202 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 58314049232250980939707) ^ 12402 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_67799354156158681010663 : Nat.Prime 67799354156158681010663 := by
  apply lucas_primality 67799354156158681010663 (5 : ZMod 67799354156158681010663)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (421, 1), (139939, 1), (738647515831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (421, 1), (139939, 1), (738647515831, 1)] : List FactorBlock).map factorBlockValue).prod) = 67799354156158681010663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_421
      · exact prime_fiftyTwoAX_139939
      · exact prime_fiftyTwoAX_738647515831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 67799354156158681010663) ^ 33899677078079340505331 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 3568387060850456895298 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 1653642784296553195382 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 161043596570448173422 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 484492201288837858 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 91788509002 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_139027313372561641588853 : Nat.Prime 139027313372561641588853 := by
  apply lucas_primality 139027313372561641588853 (2 : ZMod 139027313372561641588853)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) = 139027313372561641588853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_107
      · exact prime_fiftyTwoAX_6203
      · exact prime_fiftyTwoAX_3080389673224709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139027313372561641588853) ^ 69513656686280820794426 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 8178077257209508328756 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 1299320685724875155036 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 22412915262382982684 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 45133028 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_146436217711930766507611 : Nat.Prime 146436217711930766507611 := by
  apply lucas_primality 146436217711930766507611 (2 : ZMod 146436217711930766507611)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (179, 1), (13487, 1), (452687, 1), (262731361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (179, 1), (13487, 1), (452687, 1), (262731361, 1)] : List FactorBlock).map factorBlockValue).prod) = 146436217711930766507611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_179
      · exact prime_fiftyTwoAX_13487
      · exact prime_fiftyTwoAX_452687
      · exact prime_fiftyTwoAX_262731361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146436217711930766507611) ^ 73218108855965383253805 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 48812072570643588835870 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 29287243542386153301522 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 8613895159525339206330 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 818079428558272438590 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 10857582687916569030 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 323482268569521030 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 146436217711930766507611) ^ 557361013754010 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_186885572632985037422759 : Nat.Prime 186885572632985037422759 := by
  apply lucas_primality 186885572632985037422759 (7 : ZMod 186885572632985037422759)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (521, 1), (456068273, 1), (1518372857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (521, 1), (456068273, 1), (1518372857, 1)] : List FactorBlock).map factorBlockValue).prod) = 186885572632985037422759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_521
      · exact prime_fiftyTwoAX_456068273
      · exact prime_fiftyTwoAX_1518372857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 186885572632985037422759) ^ 93442786316492518711379 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 26697938947569291060394 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 5050961422513109119534 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 358705513690950167798 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 409775429901446 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 123082793380694 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_571541653635910918148011 : Nat.Prime 571541653635910918148011 := by
  apply lucas_primality 571541653635910918148011 (3 : ZMod 571541653635910918148011)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (431, 1), (127691, 1), (346169717796127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (431, 1), (127691, 1), (346169717796127, 1)] : List FactorBlock).map factorBlockValue).prod) = 571541653635910918148011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_431
      · exact prime_fiftyTwoAX_127691
      · exact prime_fiftyTwoAX_346169717796127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 571541653635910918148011) ^ 285770826817955459074005 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571541653635910918148011) ^ 190513884545303639382670 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571541653635910918148011) ^ 114308330727182183629602 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571541653635910918148011) ^ 1326082723053157582710 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571541653635910918148011) ^ 4475974451103922110 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 571541653635910918148011) ^ 1651044630 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_3061
      · exact prime_fiftyTwoAX_61379
      · exact prime_fiftyTwoAX_382747
      · exact prime_fiftyTwoAX_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_720252565412469632018731 : Nat.Prime 720252565412469632018731 := by
  apply lucas_primality 720252565412469632018731 (2 : ZMod 720252565412469632018731)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) = 720252565412469632018731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_661
      · exact prime_fiftyTwoAX_2220277
      · exact prime_fiftyTwoAX_5452977238001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720252565412469632018731) ^ 360126282706234816009365 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 240084188470823210672910 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 144050513082493926403746 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 1089640794875143164930 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 324397615888679490 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 132084278730 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_879700622069782613015537 : Nat.Prime 879700622069782613015537 := by
  apply lucas_primality 879700622069782613015537 (3 : ZMod 879700622069782613015537)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1607, 1), (15227, 1), (236471, 1), (9501820109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1607, 1), (15227, 1), (236471, 1), (9501820109, 1)] : List FactorBlock).map factorBlockValue).prod) = 879700622069782613015537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_1607
      · exact prime_fiftyTwoAX_15227
      · exact prime_fiftyTwoAX_236471
      · exact prime_fiftyTwoAX_9501820109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 879700622069782613015537) ^ 439850311034891306507768 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 879700622069782613015537) ^ 547417935326560431248 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 879700622069782613015537) ^ 57772418865816156368 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 879700622069782613015537) ^ 3720120530930992016 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 879700622069782613015537) ^ 92582327593904 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1121756737037619887064881 : Nat.Prime 1121756737037619887064881 := by
  apply lucas_primality 1121756737037619887064881 (6 : ZMod 1121756737037619887064881)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (251, 1), (937, 1), (59620468873578253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (251, 1), (937, 1), (59620468873578253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121756737037619887064881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_251
      · exact prime_fiftyTwoAX_937
      · exact prime_fiftyTwoAX_59620468873578253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1121756737037619887064881) ^ 560878368518809943532440 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1121756737037619887064881) ^ 224351347407523977412976 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1121756737037619887064881) ^ 4469150346763425844880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1121756737037619887064881) ^ 1197179014981451320240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1121756737037619887064881) ^ 18814960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1757163459952175319707057 : Nat.Prime 1757163459952175319707057 := by
  apply lucas_primality 1757163459952175319707057 (3 : ZMod 1757163459952175319707057)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (59, 1), (30974893, 1), (1624159326689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (59, 1), (30974893, 1), (1624159326689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1757163459952175319707057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_30974893
      · exact prime_fiftyTwoAX_1624159326689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1757163459952175319707057) ^ 878581729976087659853528 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757163459952175319707057) ^ 47490904323031765397488 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757163459952175319707057) ^ 29782431524613141011984 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757163459952175319707057) ^ 56728636962593392 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1757163459952175319707057) ^ 1081891062704 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2000581775898039632625799 : Nat.Prime 2000581775898039632625799 := by
  apply lucas_primality 2000581775898039632625799 (15 : ZMod 2000581775898039632625799)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (4017232481722971149851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (4017232481722971149851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2000581775898039632625799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_83
      · exact prime_fiftyTwoAX_4017232481722971149851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 2000581775898039632625799) ^ 1000290887949019816312899 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 666860591966013210875266 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 24103394890337826899106 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 498 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2132427262342932983371169 : Nat.Prime 2132427262342932983371169 := by
  apply lucas_primality 2132427262342932983371169 (3 : ZMod 2132427262342932983371169)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (112073585669, 1), (594594627721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (112073585669, 1), (594594627721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2132427262342932983371169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_112073585669
      · exact prime_fiftyTwoAX_594594627721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2132427262342932983371169) ^ 1066213631171466491685584 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2132427262342932983371169) ^ 19027028087072 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2132427262342932983371169) ^ 3586354741408 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_8778791656910860761186749 : Nat.Prime 8778791656910860761186749 := by
  apply lucas_primality 8778791656910860761186749 (2 : ZMod 8778791656910860761186749)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (179, 1), (283, 1), (3937057, 1), (297414308099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (179, 1), (283, 1), (3937057, 1), (297414308099, 1)] : List FactorBlock).map factorBlockValue).prod) = 8778791656910860761186749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_179
      · exact prime_fiftyTwoAX_283
      · exact prime_fiftyTwoAX_3937057
      · exact prime_fiftyTwoAX_297414308099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8778791656910860761186749) ^ 4389395828455430380593374 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8778791656910860761186749) ^ 237264639375969209761804 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8778791656910860761186749) ^ 49043528809557881347412 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8778791656910860761186749) ^ 31020465218766292442356 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8778791656910860761186749) ^ 2229785257594914364 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8778791656910860761186749) ^ 29517045474452 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_9175802682589068344864299 : Nat.Prime 9175802682589068344864299 := by
  apply lucas_primality 9175802682589068344864299 (3 : ZMod 9175802682589068344864299)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) = 9175802682589068344864299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_139027313372561641588853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9175802682589068344864299) ^ 4587901341294534172432149 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 3058600894196356114954766 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 834163880235369849533118 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 66 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_23921353297022084790113153 : Nat.Prime 23921353297022084790113153 := by
  apply lucas_primality 23921353297022084790113153 (3 : ZMod 23921353297022084790113153)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (186885572632985037422759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (186885572632985037422759, 1)] : List FactorBlock).map factorBlockValue).prod) = 23921353297022084790113153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_186885572632985037422759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 23921353297022084790113153) ^ 11960676648511042395056576 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 23921353297022084790113153) ^ 128 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_33393741430389330749913527 : Nat.Prime 33393741430389330749913527 := by
  apply lucas_primality 33393741430389330749913527 (5 : ZMod 33393741430389330749913527)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13463, 1), (33287, 1), (37257918005830523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13463, 1), (33287, 1), (37257918005830523, 1)] : List FactorBlock).map factorBlockValue).prod) = 33393741430389330749913527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_13463
      · exact prime_fiftyTwoAX_33287
      · exact prime_fiftyTwoAX_37257918005830523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33393741430389330749913527) ^ 16696870715194665374956763 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33393741430389330749913527) ^ 2480408633320161238202 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33393741430389330749913527) ^ 1003206700224992662298 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 33393741430389330749913527) ^ 896285762 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_63972817870287989501135071 : Nat.Prime 63972817870287989501135071 := by
  apply lucas_primality 63972817870287989501135071 (3 : ZMod 63972817870287989501135071)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2132427262342932983371169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2132427262342932983371169, 1)] : List FactorBlock).map factorBlockValue).prod) = 63972817870287989501135071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_2132427262342932983371169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63972817870287989501135071) ^ 31986408935143994750567535 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63972817870287989501135071) ^ 21324272623429329833711690 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63972817870287989501135071) ^ 12794563574057597900227014 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 63972817870287989501135071) ^ 30 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_116215270270976858054046887 : Nat.Prime 116215270270976858054046887 := by
  apply lucas_primality 116215270270976858054046887 (5 : ZMod 116215270270976858054046887)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (409, 1), (1579, 1), (54499, 1), (6725401, 1), (22316617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (409, 1), (1579, 1), (54499, 1), (6725401, 1), (22316617, 1)] : List FactorBlock).map factorBlockValue).prod) = 116215270270976858054046887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_409
      · exact prime_fiftyTwoAX_1579
      · exact prime_fiftyTwoAX_54499
      · exact prime_fiftyTwoAX_6725401
      · exact prime_fiftyTwoAX_22316617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 116215270270976858054046887) ^ 58107635135488429027023443 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 10565024570088805277640626 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 284144915087962978127254 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 73600551153246901870834 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 2132429407346499166114 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 17280050701954702486 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (5 : ZMod 116215270270976858054046887) ^ 5207566642873194358 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_620988666397441999096876801 : Nat.Prime 620988666397441999096876801 := by
  apply lucas_primality 620988666397441999096876801 (44 : ZMod 620988666397441999096876801)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 620988666397441999096876801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (44 : ZMod 620988666397441999096876801) ^ 310494333198720999548438400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 206996222132480666365625600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 124197733279488399819375360 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 88712666628205999870982400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 47768358953649384545913600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 36528745082202470535110400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 32683614020917999952467200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 26999507234671391265081600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 21413402289566965486099200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 20031892464433612874092800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 16783477470201135110726400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 15146065034083951197484800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 14441596892963767420857600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 13212524816966851044614400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 11716767290517773567865600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 10525231633854949137235200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (44 : ZMod 620988666397441999096876801) ^ 10180142072089213099948800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_647135557614176399058850561 : Nat.Prime 647135557614176399058850561 := by
  apply lucas_primality 647135557614176399058850561 (97 : ZMod 647135557614176399058850561)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 647135557614176399058850561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 647135557614176399058850561) ^ 323567778807088199529425280 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 215711852538058799686283520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 129427111522835279811770112 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 92447936802025199865550080 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 58830505237652399914440960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 49779658278013569158373120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 38066797506716258768167680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 28136328591920713002558720 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 22315019228075048243408640 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 20875340568199238679317760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 17490150205788551325914880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 15783794088150643879484160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 15049664130562241838577920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 13768841651365455299124480 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 12210104860644837718091520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 10968399281596210153539840 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (97 : ZMod 647135557614176399058850561) ^ 10608779633019285230472960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_749730219187155584275497601 : Nat.Prime 749730219187155584275497601 := by
  apply lucas_primality 749730219187155584275497601 (73 : ZMod 749730219187155584275497601)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 749730219187155584275497601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 749730219187155584275497601) ^ 374865109593577792137748800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 249910073062385194758499200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 149946043837431116855099520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 107104317026736512039356800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 68157292653377780388681600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 57671555322088891098115200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 44101777599244446133852800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 39459485220376609698710400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 32596966051615460185891200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 25852766178867433940534400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 24184845780230825299209600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 20262978896950150926364800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 17435586492724548471523200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 15951706791216076261180800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 14145853192210482722179200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 12707291850629755665686400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 12290659330936976791401600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1024631299555779298509846721 : Nat.Prime 1024631299555779298509846721 := by
  apply lucas_primality 1024631299555779298509846721 (67 : ZMod 1024631299555779298509846721)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024631299555779298509846721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1024631299555779298509846721) ^ 512315649777889649254923360 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 341543766518593099503282240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 204926259911155859701969344 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 146375899936539899787120960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 93148299959616299864531520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 78817792273521484500757440 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 60272429385634076382932160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 53927963134514699921570880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 44549186937207795587384640 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 35332113777785493052063680 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 33052622566315461242253120 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 27692737825831872932698560 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 24991007306238519475849920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 23828634873390216244415040 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 21800665947995304223613760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 19332666029354326386978240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 17366632195860666076438080 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 16797234418947201614915520 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_1756510799238478797445451521 : Nat.Prime 1756510799238478797445451521 := by
  apply lucas_primality 1756510799238478797445451521 (73 : ZMod 1756510799238478797445451521)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1756510799238478797445451521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 1756510799238478797445451521) ^ 878255399619239398722725760 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 585503599746159599148483840 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 351302159847695759489090304 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 250930114176925542492207360 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 159682799930770799767768320 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 135116215326036830572727040 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 103324164661086988085026560 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 92447936802025199865550080 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 76370034749499078149802240 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 60569337904775130946394880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 56661638685112219272433920 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 47473264844283210741768960 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 42841726810694604815742720 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 40849088354383227847568640 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 37372570196563378669052160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 33141713193178845234819840 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 29771369478618284702465280 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (73 : ZMod 1756510799238478797445451521) ^ 28795259003909488482712320 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2119926826667129583123820801 : Nat.Prime 2119926826667129583123820801 := by
  apply lucas_primality 2119926826667129583123820801 (67 : ZMod 2119926826667129583123820801)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2119926826667129583123820801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 2119926826667129583123820801) ^ 1059963413333564791561910400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 706642275555709861041273600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 423985365333425916624764160 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 302846689523875654731974400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 192720620606102689374892800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 163071294359009967932601600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 124701578039242916654342400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 111575096140375241217043200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 92170731594223025353209600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 68384736344100954294316800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 57295319639652150895238400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 51705532357734867881068800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 49300623875979757747065600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 45104826099300629428166400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 39998619371077916662713600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 35930963163849653951251200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (67 : ZMod 2119926826667129583123820801) ^ 34752898797821796444652800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_2276958443457287330021881601 : Nat.Prime 2276958443457287330021881601 := by
  apply lucas_primality 2276958443457287330021881601 (3 : ZMod 2276958443457287330021881601)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2276958443457287330021881601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2276958443457287330021881601) ^ 1138479221728643665010940800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 455391688691457466004376320 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 325279777636755332860268800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 206996222132480666365625600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 175150649496714410001683200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 133938731968075725295404800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 119839918076699333159046400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 98998193193795101305299200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 78515808395078873449030400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 73450272369589913871673600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 61539417390737495405996800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 55535571791641154390777600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 52952521940867147209811200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 48445924328878453830252800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 42961480065231836415507200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 38592515990801480169862400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2276958443457287330021881601) ^ 37327187597660448033145600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_3235677788070881995294252801 : Nat.Prime 3235677788070881995294252801 := by
  apply lucas_primality 3235677788070881995294252801 (76 : ZMod 3235677788070881995294252801)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3235677788070881995294252801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (76 : ZMod 3235677788070881995294252801) ^ 1617838894035440997647126400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 1078559262690293998431417600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 647135557614176399058850560 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 462239684010125999327750400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 294152526188261999572204800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 248898291390067845791865600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 190333987533581293840838400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 140681642959603565012793600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 111575096140375241217043200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 104376702840996193396588800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 87450751028942756629574400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 78918970440753219397420800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 75248320652811209192889600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 68844208256827276495622400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 61050524303224188590457600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 54841996407981050767699200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (76 : ZMod 3235677788070881995294252801) ^ 53043898165096426152364800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_20492625991115585970196934401 : Nat.Prime 20492625991115585970196934401 := by
  apply lucas_primality 20492625991115585970196934401 (79 : ZMod 20492625991115585970196934401)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 20492625991115585970196934401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 20492625991115585970196934401) ^ 10246312995557792985098467200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 6830875330371861990065644800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 4098525198223117194039386880 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 2927517998730797995742419200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 1862965999192325997290630400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 1576355845470429690015148800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 1205448587712681527658643200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 1078559262690293998431417600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 890983738744155911747692800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 706642275555709861041273600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 661052451326309224845062400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 553854756516637458653971200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 499820146124770389516998400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 476572697467804324888300800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 436013318959906084472275200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 386653320587086527739564800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 347332643917213321528761600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 20492625991115585970196934401) ^ 335944688378944032298310400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_61477877973346757910590803201 : Nat.Prime 61477877973346757910590803201 := by
  apply lucas_primality 61477877973346757910590803201 (79 : ZMod 61477877973346757910590803201)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_5
      · exact prime_fiftyTwoAX_7
      · exact prime_fiftyTwoAX_11
      · exact prime_fiftyTwoAX_13
      · exact prime_fiftyTwoAX_17
      · exact prime_fiftyTwoAX_19
      · exact prime_fiftyTwoAX_23
      · exact prime_fiftyTwoAX_29
      · exact prime_fiftyTwoAX_31
      · exact prime_fiftyTwoAX_37
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_43
      · exact prime_fiftyTwoAX_47
      · exact prime_fiftyTwoAX_53
      · exact prime_fiftyTwoAX_59
      · exact prime_fiftyTwoAX_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 61477877973346757910590803201) ^ 30738938986673378955295401600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 20492625991115585970196934400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 12295575594669351582118160640 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 8782553996192393987227257600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 5588897997576977991871891200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 4729067536411289070045446400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 3616345763138044582975929600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 3235677788070881995294252800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 2672951216232467735243078400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 2119926826667129583123820800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1983157353978927674535187200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1661564269549912375961913600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1499460438374311168550995200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1429718092403412974664902400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1308039956879718253416825600 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1159959961761259583218694400 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1041997931751639964586284800 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (79 : ZMod 61477877973346757910590803201) ^ 1007834065136832096894931200 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_61477877973346757910590803273 : Nat.Prime 61477877973346757910590803273 := by
  apply lucas_primality 61477877973346757910590803273 (7 : ZMod 61477877973346757910590803273)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_3
      · exact prime_fiftyTwoAX_12619
      · exact prime_fiftyTwoAX_212140652989
      · exact prime_fiftyTwoAX_318960960511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 61477877973346757910590803273) ^ 30738938986673378955295401636 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 61477877973346757910590803273) ^ 20492625991115585970196934424 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 61477877973346757910590803273) ^ 4871850223737757184451288 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 61477877973346757910590803273) ^ 289797721969558248 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (7 : ZMod 61477877973346757910590803273) ^ 192744208804909752 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem prime_fiftyTwoAX_61477877973346757910590803283 : Nat.Prime 61477877973346757910590803283 := by
  apply lucas_primality 61477877973346757910590803283 (2 : ZMod 61477877973346757910590803283)
  · rw [← fiftyTwoAXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (749730219187155584275497601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (749730219187155584275497601, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyTwoAX_2
      · exact prime_fiftyTwoAX_41
      · exact prime_fiftyTwoAX_749730219187155584275497601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61477877973346757910590803283) ^ 30738938986673378955295401641 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 61477877973346757910590803283) ^ 1499460438374311168550995202 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide
    · change (2 : ZMod 61477877973346757910590803283) ^ 82 ≠ 1
      rw [← fiftyTwoAXFastPow_eq_pow]
      decide

private theorem phi_fiftyTwoAX_61477877973346757910590803200 : Nat.totient 61477877973346757910590803200 = 8089711159886753248051200000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_7, prime_fiftyTwoAX_11, prime_fiftyTwoAX_13, prime_fiftyTwoAX_17, prime_fiftyTwoAX_19, prime_fiftyTwoAX_23, prime_fiftyTwoAX_29, prime_fiftyTwoAX_31, prime_fiftyTwoAX_37, prime_fiftyTwoAX_41, prime_fiftyTwoAX_43, prime_fiftyTwoAX_47, prime_fiftyTwoAX_53, prime_fiftyTwoAX_59, prime_fiftyTwoAX_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803201 : Nat.totient 61477877973346757910590803201 = 61477877973346757910590803200 := by
  rw [← show ((([(61477877973346757910590803201, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_61477877973346757910590803201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803202 : Nat.totient 61477877973346757910590803202 = 30220371431479004403054625920 := by
  rw [← show ((([(2, 1), (73, 1), (311, 1), (26828093, 1), (50467968185178619, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_73, prime_fiftyTwoAX_311, prime_fiftyTwoAX_26828093, prime_fiftyTwoAX_50467968185178619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803203 : Nat.totient 61477877973346757910590803203 = 40985251982231171940393868800 := by
  rw [← show ((([(3, 1), (20492625991115585970196934401, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_20492625991115585970196934401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803204 : Nat.totient 61477877973346757910590803204 = 30707629550436305478170016000 := by
  rw [← show ((([(2, 2), (1021, 1), (25951, 1), (1582963, 1), (366444555641737, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_1021, prime_fiftyTwoAX_25951, prime_fiftyTwoAX_1582963, prime_fiftyTwoAX_366444555641737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803205 : Nat.totient 61477877973346757910590803205 = 48244513746513956102886359040 := by
  rw [← show ((([(5, 1), (97, 1), (113, 1), (1121756737037619887064881, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_97, prime_fiftyTwoAX_113, prime_fiftyTwoAX_1121756737037619887064881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803206 : Nat.totient 61477877973346757910590803206 = 20222648962865762102412176064 := by
  rw [← show ((([(2, 1), (3, 1), (79, 1), (1913, 1), (67799354156158681010663, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_79, prime_fiftyTwoAX_1913, prime_fiftyTwoAX_67799354156158681010663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803207 : Nat.totient 61477877973346757910590803207 = 52494961528572027938864062872 := by
  rw [← show ((([(7, 1), (263, 1), (33393741430389330749913527, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_7, prime_fiftyTwoAX_263, prime_fiftyTwoAX_33393741430389330749913527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803208 : Nat.totient 61477877973346757910590803208 = 30731883709636816374692344320 := by
  rw [← show ((([(2, 3), (4357, 1), (148272073, 1), (11895479753831941, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_4357, prime_fiftyTwoAX_148272073, prime_fiftyTwoAX_11895479753831941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803209 : Nat.totient 61477877973346757910590803209 = 40939045384099444593502799808 := by
  rw [← show ((([(3, 2), (887, 1), (64809180617, 1), (118827294373519, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_887, prime_fiftyTwoAX_64809180617, prime_fiftyTwoAX_118827294373519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803210 : Nat.totient 61477877973346757910590803210 = 24495465776150614825075867648 := by
  rw [← show ((([(2, 1), (5, 1), (257, 1), (23921353297022084790113153, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_257, prime_fiftyTwoAX_23921353297022084790113153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803211 : Nat.totient 61477877973346757910590803211 = 55866866465305261528012500000 := by
  rw [← show ((([(11, 1), (3251, 1), (11351, 1), (151452027015398879101, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_11, prime_fiftyTwoAX_3251, prime_fiftyTwoAX_11351, prime_fiftyTwoAX_151452027015398879101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803212 : Nat.totient 61477877973346757910590803212 = 20491955459431952796140920128 := by
  rw [← show ((([(2, 2), (3, 1), (32029, 1), (667123, 1), (239766403692867703, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_32029, prime_fiftyTwoAX_667123, prime_fiftyTwoAX_239766403692867703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803213 : Nat.totient 61477877973346757910590803213 = 56601115595346098088695808000 := by
  rw [← show ((([(13, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_13, prime_fiftyTwoAX_401, prime_fiftyTwoAX_11069, prime_fiftyTwoAX_53269, prime_fiftyTwoAX_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803214 : Nat.totient 61477877973346757910590803214 = 26320099676472319639279216320 := by
  rw [← show ((([(2, 1), (7, 1), (967, 1), (83423, 1), (54435041108956384361, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_7, prime_fiftyTwoAX_967, prime_fiftyTwoAX_83423, prime_fiftyTwoAX_54435041108956384361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803215 : Nat.totient 61477877973346757910590803215 = 32006332603611011416288560000 := by
  rw [← show ((([(3, 1), (5, 1), (71, 1), (101, 1), (571541653635910918148011, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_71, prime_fiftyTwoAX_101, prime_fiftyTwoAX_571541653635910918148011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803216 : Nat.totient 61477877973346757910590803216 = 30565368728167527522309888000 := by
  rw [← show ((([(2, 4), (199, 1), (2311, 1), (5209, 1), (1603952514074243401, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_199, prime_fiftyTwoAX_2311, prime_fiftyTwoAX_5209, prime_fiftyTwoAX_1603952514074243401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803217 : Nat.totient 61477877973346757910590803217 = 57689836260473710230322065408 := by
  rw [← show ((([(17, 1), (337, 1), (6820433437, 1), (1573359879384229, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_17, prime_fiftyTwoAX_337, prime_fiftyTwoAX_6820433437, prime_fiftyTwoAX_1573359879384229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803218 : Nat.totient 61477877973346757910590803218 = 20466115478778701630452769280 := by
  rw [← show ((([(2, 1), (3, 2), (773, 1), (359479905341, 1), (12291142418257, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_773, prime_fiftyTwoAX_359479905341, prime_fiftyTwoAX_12291142418257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803219 : Nat.totient 61477877973346757910590803219 = 58242200185275875915296550400 := by
  rw [← show ((([(19, 1), (3235677788070881995294252801, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_19, prime_fiftyTwoAX_3235677788070881995294252801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803220 : Nat.totient 61477877973346757910590803220 = 24584937619510218369731659776 := by
  rw [← show ((([(2, 2), (5, 1), (4093, 1), (119653, 1), (6276586759550679409, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_4093, prime_fiftyTwoAX_119653, prime_fiftyTwoAX_6276586759550679409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803221 : Nat.totient 61477877973346757910590803221 = 35130215673094371907177833264 := by
  rw [← show ((([(3, 1), (7, 1), (112714183, 1), (25972933670031552247, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_7, prime_fiftyTwoAX_112714183, prime_fiftyTwoAX_25972933670031552247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803222 : Nat.totient 61477877973346757910590803222 = 27914054898917135071835712000 := by
  rw [← show ((([(2, 1), (11, 3), (1321, 1), (4091, 1), (11369, 1), (375886089384859, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_11, prime_fiftyTwoAX_1321, prime_fiftyTwoAX_4091, prime_fiftyTwoAX_11369, prime_fiftyTwoAX_375886089384859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803223 : Nat.totient 61477877973346757910590803223 = 58804926757114290175347724316 := by
  rw [← show ((([(23, 2), (116215270270976858054046887, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_23, prime_fiftyTwoAX_116215270270976858054046887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803224 : Nat.totient 61477877973346757910590803224 = 20472317461114426771057958400 := by
  rw [← show ((([(2, 3), (3, 1), (1093, 1), (21611, 1), (39791, 1), (209623, 1), (13001360959, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_1093, prime_fiftyTwoAX_21611, prime_fiftyTwoAX_39791, prime_fiftyTwoAX_209623, prime_fiftyTwoAX_13001360959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803225 : Nat.totient 61477877973346757910590803225 = 48907540909417823055779610240 := by
  rw [← show ((([(5, 2), (179, 1), (14147943049, 1), (971029727964899, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_179, prime_fiftyTwoAX_14147943049, prime_fiftyTwoAX_971029727964899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803226 : Nat.totient 61477877973346757910590803226 = 28374270226316623452091290624 := by
  rw [← show ((([(2, 1), (13, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_13, prime_fiftyTwoAX_210193, prime_fiftyTwoAX_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803227 : Nat.totient 61477877973346757910590803227 = 40985251982231171940393868800 := by
  rw [← show ((([(3, 3), (2276958443457287330021881601, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_2276958443457287330021881601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803228 : Nat.totient 61477877973346757910590803228 = 26347661988215578344867920448 := by
  rw [← show ((([(2, 2), (7, 1), (72863556869, 1), (30133561870930829, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_7, prime_fiftyTwoAX_72863556869, prime_fiftyTwoAX_30133561870930829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803229 : Nat.totient 61477877973346757910590803229 = 59357951146679628327466982400 := by
  rw [← show ((([(29, 1), (2119926826667129583123820801, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_29, prime_fiftyTwoAX_2119926826667129583123820801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803230 : Nat.totient 61477877973346757910590803230 = 16393700429161472505772529664 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (49277, 1), (242257, 1), (171663126899945669, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_49277, prime_fiftyTwoAX_242257, prime_fiftyTwoAX_171663126899945669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803231 : Nat.totient 61477877973346757910590803231 = 59494720619367830236055615100 := by
  rw [← show ((([(31, 2), (63972817870287989501135071, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_31, prime_fiftyTwoAX_63972817870287989501135071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803232 : Nat.totient 61477877973346757910590803232 = 30738938979842171026427080000 := by
  rw [← show ((([(2, 5), (4499780951, 1), (426950491054489151, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_4499780951, prime_fiftyTwoAX_426950491054489151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803233 : Nat.totient 61477877973346757910590803233 = 36420080831243025410713190400 := by
  rw [← show ((([(3, 1), (11, 1), (67, 1), (131, 1), (13633, 1), (129593, 1), (120139508808577, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_11, prime_fiftyTwoAX_67, prime_fiftyTwoAX_131, prime_fiftyTwoAX_13633, prime_fiftyTwoAX_129593, prime_fiftyTwoAX_120139508808577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803234 : Nat.totient 61477877973346757910590803234 = 28778249948022726534635016960 := by
  rw [← show ((([(2, 1), (17, 1), (191, 1), (27509, 1), (344137326892735588579, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_17, prime_fiftyTwoAX_191, prime_fiftyTwoAX_27509, prime_fiftyTwoAX_344137326892735588579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803235 : Nat.totient 61477877973346757910590803235 = 42156259181723491138690836480 := by
  rw [← show ((([(5, 1), (7, 1), (1756510799238478797445451521, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_7, prime_fiftyTwoAX_1756510799238478797445451521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803236 : Nat.totient 61477877973346757910590803236 = 20483982960330636334612681200 := by
  rw [← show ((([(2, 2), (3, 2), (2371, 1), (720252565412469632018731, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_2371, prime_fiftyTwoAX_720252565412469632018731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803237 : Nat.totient 61477877973346757910590803237 = 59816313703790362831008992400 := by
  rw [← show ((([(37, 1), (9755571039311, 1), (170319529513391, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_37, prime_fiftyTwoAX_9755571039311, prime_fiftyTwoAX_170319529513391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803238 : Nat.totient 61477877973346757910590803238 = 29100974921835489007682014080 := by
  rw [← show ((([(2, 1), (19, 1), (1447, 1), (1908980081, 1), (585686675729543, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_19, prime_fiftyTwoAX_1447, prime_fiftyTwoAX_1908980081, prime_fiftyTwoAX_585686675729543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803239 : Nat.totient 61477877973346757910590803239 = 37832540291290312560363571200 := by
  rw [← show ((([(3, 1), (13, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_13, prime_fiftyTwoAX_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803240 : Nat.totient 61477877973346757910590803240 = 24591091666920958765336441600 := by
  rw [← show ((([(2, 3), (5, 1), (413141, 1), (3720151109024930829341, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_413141, prime_fiftyTwoAX_3720151109024930829341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803241 : Nat.totient 61477877973346757910590803241 = 59971200456465485185590720000 := by
  rw [← show ((([(41, 1), (8311, 1), (183112561, 1), (985288906104631, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_41, prime_fiftyTwoAX_8311, prime_fiftyTwoAX_183112561, prime_fiftyTwoAX_985288906104631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803242 : Nat.totient 61477877973346757910590803242 = 17565107992158670786832772144 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (77681756927, 1), (18843021286721663, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_7, prime_fiftyTwoAX_77681756927, prime_fiftyTwoAX_18843021286721663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803243 : Nat.totient 61477877973346757910590803243 = 60048155875114743687204313824 := by
  rw [← show ((([(43, 1), (14990197, 1), (95376871458287904733, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_43, prime_fiftyTwoAX_14990197, prime_fiftyTwoAX_95376871458287904733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803244 : Nat.totient 61477877973346757910590803244 = 27944447496647127971048584640 := by
  rw [← show ((([(2, 2), (11, 1), (657653, 1), (2124561888099414885917, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_11, prime_fiftyTwoAX_657653, prime_fiftyTwoAX_2124561888099414885917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803245 : Nat.totient 61477877973346757910590803245 = 32767088770855262769602684928 := by
  rw [← show ((([(3, 2), (5, 1), (1553, 1), (879700622069782613015537, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_1553, prime_fiftyTwoAX_879700622069782613015537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803246 : Nat.totient 61477877973346757910590803246 = 29280266722511589567984537600 := by
  rw [← show ((([(2, 1), (23, 1), (241, 1), (150377, 1), (1595647661, 1), (23111364013, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_23, prime_fiftyTwoAX_241, prime_fiftyTwoAX_150377, prime_fiftyTwoAX_1595647661, prime_fiftyTwoAX_23111364013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803247 : Nat.totient 61477877973346757910590803247 = 59766013600249140062159380384 := by
  rw [← show ((([(47, 1), (149, 1), (8778791656910860761186749, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_47, prime_fiftyTwoAX_149, prime_fiftyTwoAX_8778791656910860761186749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803248 : Nat.totient 61477877973346757910590803248 = 20492625866677710968562681600 := by
  rw [← show ((([(2, 4), (3, 1), (164681581, 1), (7777367187437459221, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_164681581, prime_fiftyTwoAX_7777367187437459221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803249 : Nat.totient 61477877973346757910590803249 = 52694101149224603768257116384 := by
  rw [← show ((([(7, 2), (43093, 1), (29114950708575121538557, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_7, prime_fiftyTwoAX_43093, prime_fiftyTwoAX_29114950708575121538557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803250 : Nat.totient 61477877973346757910590803250 = 24294252918783809640956094400 := by
  rw [← show ((([(2, 1), (5, 3), (83, 1), (39227, 1), (75529336934262770093, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_83, prime_fiftyTwoAX_39227, prime_fiftyTwoAX_75529336934262770093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803251 : Nat.totient 61477877973346757910590803251 = 38573490705311514272300236800 := by
  rw [← show ((([(3, 1), (17, 1), (44641, 1), (27003171696706649216161, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_17, prime_fiftyTwoAX_44641, prime_fiftyTwoAX_27003171696706649216161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803252 : Nat.totient 61477877973346757910590803252 = 28093315868479095348023428608 := by
  rw [← show ((([(2, 2), (13, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_13, prime_fiftyTwoAX_103, prime_fiftyTwoAX_5009, prime_fiftyTwoAX_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803253 : Nat.totient 61477877973346757910590803253 = 60316078851050949460059342336 := by
  rw [← show ((([(53, 1), (32797, 1), (1920695069, 1), (18414098321657, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_53, prime_fiftyTwoAX_32797, prime_fiftyTwoAX_1920695069, prime_fiftyTwoAX_18414098321657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803254 : Nat.totient 61477877973346757910590803254 = 20427333104965878549299681280 := by
  rw [← show ((([(2, 1), (3, 5), (563, 1), (971, 1), (4397, 1), (8117, 1), (30853, 1), (210138469, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_563, prime_fiftyTwoAX_971, prime_fiftyTwoAX_4397, prime_fiftyTwoAX_8117, prime_fiftyTwoAX_30853, prime_fiftyTwoAX_210138469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803255 : Nat.totient 61477877973346757910590803255 = 44604474703862093592785896320 := by
  rw [← show ((([(5, 1), (11, 1), (419, 1), (6273351317, 1), (425248261460767, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_11, prime_fiftyTwoAX_419, prime_fiftyTwoAX_6273351317, prime_fiftyTwoAX_425248261460767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803256 : Nat.totient 61477877973346757910590803256 = 26347661673078445514593005696 := by
  rw [← show ((([(2, 3), (7, 1), (83511149, 1), (13145780685211854149, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_7, prime_fiftyTwoAX_83511149, prime_fiftyTwoAX_13145780685211854149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803257 : Nat.totient 61477877973346757910590803257 = 38792261138344403165265065472 := by
  rw [← show ((([(3, 1), (19, 1), (1523, 1), (3739, 1), (189403780999497233633, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_19, prime_fiftyTwoAX_1523, prime_fiftyTwoAX_3739, prime_fiftyTwoAX_189403780999497233633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803258 : Nat.totient 61477877973346757910590803258 = 29655516575435572039625293824 := by
  rw [← show ((([(2, 1), (29, 1), (1279, 1), (128257, 1), (1292293, 1), (5000095063219, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_29, prime_fiftyTwoAX_1279, prime_fiftyTwoAX_128257, prime_fiftyTwoAX_1292293, prime_fiftyTwoAX_5000095063219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803259 : Nat.totient 61477877973346757910590803259 = 60333964560917891777461474816 := by
  rw [← show ((([(59, 1), (593, 1), (1757163459952175319707057, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_59, prime_fiftyTwoAX_593, prime_fiftyTwoAX_1757163459952175319707057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803260 : Nat.totient 61477877973346757910590803260 = 16394100792892468776157547520 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1024631299555779298509846721, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_1024631299555779298509846721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803261 : Nat.totient 61477877973346757910590803261 = 60456787021601719766507911680 := by
  rw [← show ((([(61, 1), (4649, 1), (248719, 1), (9017237, 1), (96660055483, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_61, prime_fiftyTwoAX_4649, prime_fiftyTwoAX_248719, prime_fiftyTwoAX_9017237, prime_fiftyTwoAX_96660055483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803262 : Nat.totient 61477877973346757910590803262 = 29701488066383792443591584000 := by
  rw [← show ((([(2, 1), (31, 1), (653, 1), (94651, 1), (8429209, 1), (1903276866263, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_31, prime_fiftyTwoAX_653, prime_fiftyTwoAX_94651, prime_fiftyTwoAX_8429209, prime_fiftyTwoAX_1903276866263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803263 : Nat.totient 61477877973346757910590803263 = 35127677911667361644079525888 := by
  rw [← show ((([(3, 2), (7, 1), (14057, 1), (901937, 1), (76967870515442089, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_7, prime_fiftyTwoAX_14057, prime_fiftyTwoAX_901937, prime_fiftyTwoAX_76967870515442089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803264 : Nat.totient 61477877973346757910590803264 = 30732170420738520870771253248 := by
  rw [← show ((([(2, 6), (7057, 1), (15373, 1), (74323, 1), (119134327776067, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_7057, prime_fiftyTwoAX_15373, prime_fiftyTwoAX_74323, prime_fiftyTwoAX_119134327776067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803265 : Nat.totient 61477877973346757910590803265 = 44930360277427434834718848000 := by
  rw [← show ((([(5, 1), (13, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_13, prime_fiftyTwoAX_107, prime_fiftyTwoAX_1013, prime_fiftyTwoAX_144417341, prime_fiftyTwoAX_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803266 : Nat.totient 61477877973346757910590803266 = 18629639130999750387931008000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (893041, 1), (1043046175479247871761, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_11, prime_fiftyTwoAX_893041, prime_fiftyTwoAX_1043046175479247871761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803267 : Nat.totient 61477877973346757910590803267 = 61375322133804936021569925120 := by
  rw [← show ((([(691, 1), (5647, 1), (39719, 1), (52457, 1), (7561731942337, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_691, prime_fiftyTwoAX_5647, prime_fiftyTwoAX_39719, prime_fiftyTwoAX_52457, prime_fiftyTwoAX_7561731942337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803268 : Nat.totient 61477877973346757910590803268 = 28925638429639155373696665600 := by
  rw [← show ((([(2, 2), (17, 1), (9437, 1), (20023, 1), (46861, 1), (102102247358591, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_17, prime_fiftyTwoAX_9437, prime_fiftyTwoAX_20023, prime_fiftyTwoAX_46861, prime_fiftyTwoAX_102102247358591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803269 : Nat.totient 61477877973346757910590803269 = 39105557387609635615739904000 := by
  rw [← show ((([(3, 1), (23, 1), (683, 1), (997, 1), (52183, 1), (124001, 1), (202208629297, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_23, prime_fiftyTwoAX_683, prime_fiftyTwoAX_997, prime_fiftyTwoAX_52183, prime_fiftyTwoAX_124001, prime_fiftyTwoAX_202208629297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803270 : Nat.totient 61477877973346757910590803270 = 21030115628240192618162388576 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (439, 1), (2000581775898039632625799, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_7, prime_fiftyTwoAX_439, prime_fiftyTwoAX_2000581775898039632625799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803271 : Nat.totient 61477877973346757910590803271 = 61477870843775968710965867520 := by
  rw [← show ((([(8634161, 1), (6678008737, 1), (1066232074903, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_8634161, prime_fiftyTwoAX_6678008737, prime_fiftyTwoAX_1066232074903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803272 : Nat.totient 61477877973346757910590803272 = 20491002040880172153982988160 := by
  rw [← show ((([(2, 3), (3, 2), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_12619, prime_fiftyTwoAX_212140652989, prime_fiftyTwoAX_318960960511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803273 : Nat.totient 61477877973346757910590803273 = 61477877973346757910590803272 := by
  rw [← show ((([(61477877973346757910590803273, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_61477877973346757910590803273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803274 : Nat.totient 61477877973346757910590803274 = 29906071351804154695159454400 := by
  rw [← show ((([(2, 1), (37, 1), (14341, 1), (57930558174113115402061, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_37, prime_fiftyTwoAX_14341, prime_fiftyTwoAX_57930558174113115402061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803275 : Nat.totient 61477877973346757910590803275 = 32000638476019879449234984960 := by
  rw [← show ((([(3, 1), (5, 2), (73, 1), (127, 1), (383, 1), (174255157, 1), (1324788685877, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_73, prime_fiftyTwoAX_127, prime_fiftyTwoAX_383, prime_fiftyTwoAX_174255157, prime_fiftyTwoAX_1324788685877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803276 : Nat.totient 61477877973346757910590803276 = 29112267051024473456475192000 := by
  rw [← show ((([(2, 2), (19, 1), (3391, 1), (118691, 1), (2009831726809906421, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_19, prime_fiftyTwoAX_3391, prime_fiftyTwoAX_118691, prime_fiftyTwoAX_2009831726809906421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803277 : Nat.totient 61477877973346757910590803277 = 47897152832845846664526551040 := by
  rw [← show ((([(7, 1), (11, 1), (6247, 1), (3684697, 1), (8431793, 1), (4113721823, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_7, prime_fiftyTwoAX_11, prime_fiftyTwoAX_6247, prime_fiftyTwoAX_3684697, prime_fiftyTwoAX_8431793, prime_fiftyTwoAX_4113721823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803278 : Nat.totient 61477877973346757910590803278 = 18858596751130786945731072000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_13, prime_fiftyTwoAX_421, prime_fiftyTwoAX_1483, prime_fiftyTwoAX_2072201, prime_fiftyTwoAX_2567179, prime_fiftyTwoAX_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803279 : Nat.totient 61477877973346757910590803279 = 61471716769636948874342563840 := by
  rw [← show ((([(19457, 1), (21563, 1), (408209, 1), (358964277063341, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_19457, prime_fiftyTwoAX_21563, prime_fiftyTwoAX_408209, prime_fiftyTwoAX_358964277063341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803280 : Nat.totient 61477877973346757910590803280 = 24589867230337489669011456000 := by
  rw [← show ((([(2, 4), (5, 1), (19387, 1), (1584001, 1), (25024350819790243, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_19387, prime_fiftyTwoAX_1584001, prime_fiftyTwoAX_25024350819790243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803281 : Nat.totient 61477877973346757910590803281 = 40366020431137821717234147840 := by
  rw [← show ((([(3, 3), (137, 1), (163, 1), (631, 1), (6599, 1), (155203, 1), (157775415859, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_137, prime_fiftyTwoAX_163, prime_fiftyTwoAX_631, prime_fiftyTwoAX_6599, prime_fiftyTwoAX_155203, prime_fiftyTwoAX_157775415859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803282 : Nat.totient 61477877973346757910590803282 = 29989208767486223371019904000 := by
  rw [← show ((([(2, 1), (41, 1), (749730219187155584275497601, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_41, prime_fiftyTwoAX_749730219187155584275497601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803283 : Nat.totient 61477877973346757910590803283 = 61477877973346757910590803282 := by
  rw [← show ((([(61477877973346757910590803283, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_61477877973346757910590803283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803284 : Nat.totient 61477877973346757910590803284 = 17476561880549206765013214720 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (211, 1), (3299, 1), (1160494157, 1), (906007626637, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_7, prime_fiftyTwoAX_211, prime_fiftyTwoAX_3299, prime_fiftyTwoAX_1160494157, prime_fiftyTwoAX_906007626637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803285 : Nat.totient 61477877973346757910590803285 = 45412182467713915908757926912 := by
  rw [← show ((([(5, 1), (17, 1), (79, 1), (157, 1), (58314049232250980939707, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_17, prime_fiftyTwoAX_79, prime_fiftyTwoAX_157, prime_fiftyTwoAX_58314049232250980939707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803286 : Nat.totient 61477877973346757910590803286 = 29601155396838958526662992000 := by
  rw [← show ((([(2, 1), (43, 1), (71, 1), (590437, 1), (693751151, 1), (24580164613, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_43, prime_fiftyTwoAX_71, prime_fiftyTwoAX_590437, prime_fiftyTwoAX_693751151, prime_fiftyTwoAX_24580164613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803287 : Nat.totient 61477877973346757910590803287 = 39365709087523488693617664000 := by
  rw [← show ((([(3, 1), (29, 1), (193, 1), (32237, 1), (36769511, 1), (3088871442451, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_29, prime_fiftyTwoAX_193, prime_fiftyTwoAX_32237, prime_fiftyTwoAX_36769511, prime_fiftyTwoAX_3088871442451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803288 : Nat.totient 61477877973346757910590803288 = 27627104415485130324189696000 := by
  rw [← show ((([(2, 3), (11, 1), (89, 1), (12301, 1), (24019, 1), (4553573, 1), (5834431507, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_11, prime_fiftyTwoAX_89, prime_fiftyTwoAX_12301, prime_fiftyTwoAX_24019, prime_fiftyTwoAX_4553573, prime_fiftyTwoAX_5834431507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803289 : Nat.totient 61477877973346757910590803289 = 61467261857709824865250105200 := by
  rw [← show ((([(5791, 1), (7465557739, 1), (1422011291666261, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5791, prime_fiftyTwoAX_7465557739, prime_fiftyTwoAX_1422011291666261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803290 : Nat.totient 61477877973346757910590803290 = 16393498002114335435392245888 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (27197, 1), (25116282422222531860373, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_5, prime_fiftyTwoAX_27197, prime_fiftyTwoAX_25116282422222531860373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803291 : Nat.totient 61477877973346757910590803291 = 48597088816805298326323163424 := by
  rw [← show ((([(7, 1), (13, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_7, prime_fiftyTwoAX_13, prime_fiftyTwoAX_1087, prime_fiftyTwoAX_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803292 : Nat.totient 61477877973346757910590803292 = 29402457658363737319269446208 := by
  rw [← show ((([(2, 2), (23, 1), (5140117, 1), (130004395631094960253, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_23, prime_fiftyTwoAX_5140117, prime_fiftyTwoAX_130004395631094960253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803293 : Nat.totient 61477877973346757910590803293 = 39662945489004276467685750000 := by
  rw [← show ((([(3, 1), (31, 1), (196751, 1), (3359842904617050103151, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_31, prime_fiftyTwoAX_196751, prime_fiftyTwoAX_3359842904617050103151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803294 : Nat.totient 61477877973346757910590803294 = 29883707048457299433432837600 := by
  rw [← show ((([(2, 1), (47, 1), (151, 1), (15139, 1), (286099355001209160109, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_47, prime_fiftyTwoAX_151, prime_fiftyTwoAX_15139, prime_fiftyTwoAX_286099355001209160109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803295 : Nat.totient 61477877973346757910590803295 = 46593760148220700732237240320 := by
  rw [← show ((([(5, 1), (19, 1), (647135557614176399058850561, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_5, prime_fiftyTwoAX_19, prime_fiftyTwoAX_647135557614176399058850561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803296 : Nat.totient 61477877973346757910590803296 = 20477772934683623251292998656 := by
  rw [← show ((([(2, 5), (3, 1), (1907, 1), (4987, 1), (67337590816601618489, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_3, prime_fiftyTwoAX_1907, prime_fiftyTwoAX_4987, prime_fiftyTwoAX_67337590816601618489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803297 : Nat.totient 61477877973346757910590803297 = 61477731537129045979823875860 := by
  rw [← show ((([(419827, 1), (146436217711930766507611, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_419827, prime_fiftyTwoAX_146436217711930766507611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803298 : Nat.totient 61477877973346757910590803298 = 26347658517212423435352000000 := by
  rw [← show ((([(2, 1), (7, 2), (7590001, 1), (82651541869666928401, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_7, prime_fiftyTwoAX_7590001, prime_fiftyTwoAX_82651541869666928401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803299 : Nat.totient 61477877973346757910590803299 = 37259319983846519945812608000 := by
  rw [← show ((([(3, 2), (11, 1), (620988666397441999096876801, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_3, prime_fiftyTwoAX_11, prime_fiftyTwoAX_620988666397441999096876801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyTwoAX_61477877973346757910590803300 : Nat.totient 61477877973346757910590803300 = 24224119082035140430441746720 := by
  rw [← show ((([(2, 2), (5, 2), (67, 1), (9175802682589068344864299, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477877973346757910590803300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyTwoAX_2, prime_fiftyTwoAX_5, prime_fiftyTwoAX_67, prime_fiftyTwoAX_9175802682589068344864299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyTwoAX : certifiedKill 1 61477877973346757910590803199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyTwoAX_61477877973346757910590803200, phi_fiftyTwoAX_61477877973346757910590803201, phi_fiftyTwoAX_61477877973346757910590803202,
    phi_fiftyTwoAX_61477877973346757910590803203, phi_fiftyTwoAX_61477877973346757910590803204, phi_fiftyTwoAX_61477877973346757910590803205,
    phi_fiftyTwoAX_61477877973346757910590803206, phi_fiftyTwoAX_61477877973346757910590803207, phi_fiftyTwoAX_61477877973346757910590803208,
    phi_fiftyTwoAX_61477877973346757910590803209, phi_fiftyTwoAX_61477877973346757910590803210, phi_fiftyTwoAX_61477877973346757910590803211,
    phi_fiftyTwoAX_61477877973346757910590803212, phi_fiftyTwoAX_61477877973346757910590803213, phi_fiftyTwoAX_61477877973346757910590803214,
    phi_fiftyTwoAX_61477877973346757910590803215, phi_fiftyTwoAX_61477877973346757910590803216, phi_fiftyTwoAX_61477877973346757910590803217,
    phi_fiftyTwoAX_61477877973346757910590803218, phi_fiftyTwoAX_61477877973346757910590803219, phi_fiftyTwoAX_61477877973346757910590803220,
    phi_fiftyTwoAX_61477877973346757910590803221, phi_fiftyTwoAX_61477877973346757910590803222, phi_fiftyTwoAX_61477877973346757910590803223,
    phi_fiftyTwoAX_61477877973346757910590803224, phi_fiftyTwoAX_61477877973346757910590803225, phi_fiftyTwoAX_61477877973346757910590803226,
    phi_fiftyTwoAX_61477877973346757910590803227, phi_fiftyTwoAX_61477877973346757910590803228, phi_fiftyTwoAX_61477877973346757910590803229,
    phi_fiftyTwoAX_61477877973346757910590803230, phi_fiftyTwoAX_61477877973346757910590803231, phi_fiftyTwoAX_61477877973346757910590803232,
    phi_fiftyTwoAX_61477877973346757910590803233, phi_fiftyTwoAX_61477877973346757910590803234, phi_fiftyTwoAX_61477877973346757910590803235,
    phi_fiftyTwoAX_61477877973346757910590803236, phi_fiftyTwoAX_61477877973346757910590803237, phi_fiftyTwoAX_61477877973346757910590803238,
    phi_fiftyTwoAX_61477877973346757910590803239, phi_fiftyTwoAX_61477877973346757910590803240, phi_fiftyTwoAX_61477877973346757910590803241,
    phi_fiftyTwoAX_61477877973346757910590803242, phi_fiftyTwoAX_61477877973346757910590803243, phi_fiftyTwoAX_61477877973346757910590803244,
    phi_fiftyTwoAX_61477877973346757910590803245, phi_fiftyTwoAX_61477877973346757910590803246, phi_fiftyTwoAX_61477877973346757910590803247,
    phi_fiftyTwoAX_61477877973346757910590803248, phi_fiftyTwoAX_61477877973346757910590803249, phi_fiftyTwoAX_61477877973346757910590803250,
    phi_fiftyTwoAX_61477877973346757910590803251, phi_fiftyTwoAX_61477877973346757910590803252, phi_fiftyTwoAX_61477877973346757910590803253,
    phi_fiftyTwoAX_61477877973346757910590803254, phi_fiftyTwoAX_61477877973346757910590803255, phi_fiftyTwoAX_61477877973346757910590803256,
    phi_fiftyTwoAX_61477877973346757910590803257, phi_fiftyTwoAX_61477877973346757910590803258, phi_fiftyTwoAX_61477877973346757910590803259,
    phi_fiftyTwoAX_61477877973346757910590803260, phi_fiftyTwoAX_61477877973346757910590803261, phi_fiftyTwoAX_61477877973346757910590803262,
    phi_fiftyTwoAX_61477877973346757910590803263, phi_fiftyTwoAX_61477877973346757910590803264, phi_fiftyTwoAX_61477877973346757910590803265,
    phi_fiftyTwoAX_61477877973346757910590803266, phi_fiftyTwoAX_61477877973346757910590803267, phi_fiftyTwoAX_61477877973346757910590803268,
    phi_fiftyTwoAX_61477877973346757910590803269, phi_fiftyTwoAX_61477877973346757910590803270, phi_fiftyTwoAX_61477877973346757910590803271,
    phi_fiftyTwoAX_61477877973346757910590803272, phi_fiftyTwoAX_61477877973346757910590803273, phi_fiftyTwoAX_61477877973346757910590803274,
    phi_fiftyTwoAX_61477877973346757910590803275, phi_fiftyTwoAX_61477877973346757910590803276, phi_fiftyTwoAX_61477877973346757910590803277,
    phi_fiftyTwoAX_61477877973346757910590803278, phi_fiftyTwoAX_61477877973346757910590803279, phi_fiftyTwoAX_61477877973346757910590803280,
    phi_fiftyTwoAX_61477877973346757910590803281, phi_fiftyTwoAX_61477877973346757910590803282, phi_fiftyTwoAX_61477877973346757910590803283,
    phi_fiftyTwoAX_61477877973346757910590803284, phi_fiftyTwoAX_61477877973346757910590803285, phi_fiftyTwoAX_61477877973346757910590803286,
    phi_fiftyTwoAX_61477877973346757910590803287, phi_fiftyTwoAX_61477877973346757910590803288, phi_fiftyTwoAX_61477877973346757910590803289,
    phi_fiftyTwoAX_61477877973346757910590803290, phi_fiftyTwoAX_61477877973346757910590803291, phi_fiftyTwoAX_61477877973346757910590803292,
    phi_fiftyTwoAX_61477877973346757910590803293, phi_fiftyTwoAX_61477877973346757910590803294, phi_fiftyTwoAX_61477877973346757910590803295,
    phi_fiftyTwoAX_61477877973346757910590803296, phi_fiftyTwoAX_61477877973346757910590803297, phi_fiftyTwoAX_61477877973346757910590803298,
    phi_fiftyTwoAX_61477877973346757910590803299, phi_fiftyTwoAX_61477877973346757910590803300]

end TotientTailPeriodKiller
end Erdos249257
