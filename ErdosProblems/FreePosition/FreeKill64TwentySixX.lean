import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open private
  prime_t64_2
  prime_t64_3
  prime_t64_5
  prime_t64_7
  prime_t64_11
  prime_t64_13
  prime_t64_17
  prime_t64_19
  prime_t64_23
  prime_t64_29
  prime_t64_31
  prime_t64_37
  prime_t64_41
  prime_t64_43
  prime_t64_47
  prime_t64_53
  prime_t64_59
  prime_t64_61
  prime_t64_67
  prime_t64_71
  prime_t64_73
  prime_t64_79
  prime_t64_83
  prime_t64_89
  prime_t64_97
  prime_t64_101
  prime_t64_103
  prime_t64_107
  prime_t64_113
  prime_t64_137
  prime_t64_139
  prime_t64_149
  prime_t64_157
  prime_t64_167
  prime_t64_179
  prime_t64_191
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_227
  prime_t64_229
  prime_t64_239
  prime_t64_251
  prime_t64_307
  prime_t64_311
  prime_t64_317
  prime_t64_421
  prime_t64_439
  prime_t64_479
  prime_t64_491
  prime_t64_499
  prime_t64_521
  prime_t64_563
  prime_t64_661
  prime_t64_673
  prime_t64_719
  prime_t64_859
  prime_t64_991
  prime_t64_1051
  prime_t64_1093
  prime_t64_1153
  prime_t64_1229
  prime_t64_1373
  prime_t64_1409
  prime_t64_1483
  prime_t64_1801
  prime_t64_4327
  prime_t64_5009
  prime_t64_97523
  prime_t64_210193
  prime_t64_1214459
  prime_t64_2072201
  prime_t64_2567179
  from Erdos249257.DiagonalPincerCertificatesT64

private def twentySixXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentySixXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentySixXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentySixXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentySixXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentySixXFastPow a n * twentySixXFastPow a n * a
        else twentySixXFastPow a n * twentySixXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentySixX_127 : Nat.Prime 127 := by norm_num

private theorem prime_twentySixX_131 : Nat.Prime 131 := by norm_num

private theorem prime_twentySixX_151 : Nat.Prime 151 := by norm_num

private theorem prime_twentySixX_173 : Nat.Prime 173 := by norm_num

private theorem prime_twentySixX_181 : Nat.Prime 181 := by norm_num

private theorem prime_twentySixX_199 : Nat.Prime 199 := by norm_num

private theorem prime_twentySixX_211 : Nat.Prime 211 := by norm_num

private theorem prime_twentySixX_241 : Nat.Prime 241 := by norm_num

private theorem prime_twentySixX_257 : Nat.Prime 257 := by norm_num

private theorem prime_twentySixX_271 : Nat.Prime 271 := by norm_num

private theorem prime_twentySixX_277 : Nat.Prime 277 := by norm_num

private theorem prime_twentySixX_293 : Nat.Prime 293 := by norm_num

private theorem prime_twentySixX_313 : Nat.Prime 313 := by norm_num

private theorem prime_twentySixX_331 : Nat.Prime 331 := by norm_num

private theorem prime_twentySixX_347 : Nat.Prime 347 := by norm_num

private theorem prime_twentySixX_359 : Nat.Prime 359 := by norm_num

private theorem prime_twentySixX_367 : Nat.Prime 367 := by norm_num

private theorem prime_twentySixX_373 : Nat.Prime 373 := by norm_num

private theorem prime_twentySixX_401 : Nat.Prime 401 := by norm_num

private theorem prime_twentySixX_443 : Nat.Prime 443 := by norm_num

private theorem prime_twentySixX_457 : Nat.Prime 457 := by norm_num

private theorem prime_twentySixX_463 : Nat.Prime 463 := by norm_num

private theorem prime_twentySixX_487 : Nat.Prime 487 := by norm_num

private theorem prime_twentySixX_503 : Nat.Prime 503 := by norm_num

private theorem prime_twentySixX_523 : Nat.Prime 523 := by norm_num

private theorem prime_twentySixX_557 : Nat.Prime 557 := by norm_num

private theorem prime_twentySixX_577 : Nat.Prime 577 := by norm_num

private theorem prime_twentySixX_613 : Nat.Prime 613 := by norm_num

private theorem prime_twentySixX_643 : Nat.Prime 643 := by norm_num

private theorem prime_twentySixX_653 : Nat.Prime 653 := by norm_num

private theorem prime_twentySixX_677 : Nat.Prime 677 := by norm_num

private theorem prime_twentySixX_733 : Nat.Prime 733 := by norm_num

private theorem prime_twentySixX_773 : Nat.Prime 773 := by norm_num

private theorem prime_twentySixX_821 : Nat.Prime 821 := by norm_num

private theorem prime_twentySixX_967 : Nat.Prime 967 := by norm_num

private theorem prime_twentySixX_971 : Nat.Prime 971 := by norm_num

private theorem prime_twentySixX_977 : Nat.Prime 977 := by norm_num

private theorem prime_twentySixX_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_twentySixX_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_twentySixX_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_twentySixX_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_twentySixX_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_twentySixX_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_twentySixX_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_twentySixX_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_twentySixX_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_twentySixX_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_twentySixX_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_twentySixX_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_twentySixX_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_twentySixX_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_twentySixX_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_twentySixX_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_twentySixX_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_twentySixX_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_twentySixX_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_twentySixX_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_twentySixX_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_twentySixX_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_twentySixX_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_twentySixX_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_twentySixX_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_twentySixX_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_twentySixX_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_twentySixX_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_twentySixX_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_twentySixX_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_twentySixX_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_twentySixX_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_twentySixX_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_twentySixX_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_twentySixX_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_twentySixX_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_twentySixX_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_twentySixX_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_twentySixX_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_twentySixX_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_twentySixX_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_twentySixX_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_twentySixX_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_twentySixX_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_twentySixX_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_twentySixX_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_twentySixX_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_twentySixX_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_twentySixX_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_twentySixX_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_twentySixX_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_twentySixX_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_twentySixX_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_twentySixX_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_twentySixX_3919 : Nat.Prime 3919 := by norm_num

private theorem prime_twentySixX_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_twentySixX_4079 : Nat.Prime 4079 := by norm_num

private theorem prime_twentySixX_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_twentySixX_4093 : Nat.Prime 4093 := by norm_num

private theorem prime_twentySixX_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_twentySixX_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_twentySixX_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_twentySixX_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_twentySixX_4597 : Nat.Prime 4597 := by norm_num

private theorem prime_twentySixX_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_twentySixX_4987 : Nat.Prime 4987 := by norm_num

private theorem prime_twentySixX_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_twentySixX_5167 : Nat.Prime 5167 := by norm_num

private theorem prime_twentySixX_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_twentySixX_5387 : Nat.Prime 5387 := by norm_num

private theorem prime_twentySixX_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_twentySixX_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_twentySixX_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_twentySixX_6203 : Nat.Prime 6203 := by norm_num

private theorem prime_twentySixX_6287 : Nat.Prime 6287 := by norm_num

private theorem prime_twentySixX_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_twentySixX_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_twentySixX_6563 : Nat.Prime 6563 := by norm_num

private theorem prime_twentySixX_6709 : Nat.Prime 6709 := by norm_num

private theorem prime_twentySixX_6947 : Nat.Prime 6947 := by norm_num

private theorem prime_twentySixX_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_twentySixX_7057 : Nat.Prime 7057 := by norm_num

private theorem prime_twentySixX_7219 : Nat.Prime 7219 := by norm_num

private theorem prime_twentySixX_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_twentySixX_8117 : Nat.Prime 8117 := by norm_num

private theorem prime_twentySixX_8669 : Nat.Prime 8669 := by norm_num

private theorem prime_twentySixX_8783 : Nat.Prime 8783 := by norm_num

private theorem prime_twentySixX_9437 : Nat.Prime 9437 := by norm_num

private theorem prime_twentySixX_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_twentySixX_10159 : Nat.Prime 10159 := by norm_num

private theorem prime_twentySixX_10631 : Nat.Prime 10631 := by norm_num

private theorem prime_twentySixX_10861 : Nat.Prime 10861 := by norm_num

private theorem prime_twentySixX_11369 : Nat.Prime 11369 := by norm_num

private theorem prime_twentySixX_11423 : Nat.Prime 11423 := by norm_num

private theorem prime_twentySixX_12301 : Nat.Prime 12301 := by norm_num

private theorem prime_twentySixX_12553 : Nat.Prime 12553 := by norm_num

private theorem prime_twentySixX_12569 : Nat.Prime 12569 := by norm_num

private theorem prime_twentySixX_12619 : Nat.Prime 12619 := by norm_num

private theorem prime_twentySixX_13567 : Nat.Prime 13567 := by norm_num

private theorem prime_twentySixX_14341 : Nat.Prime 14341 := by norm_num

private theorem prime_twentySixX_14419 : Nat.Prime 14419 := by norm_num

private theorem prime_twentySixX_15101 : Nat.Prime 15101 := by norm_num

private theorem prime_twentySixX_15139 : Nat.Prime 15139 := by norm_num

private theorem prime_twentySixX_15373 : Nat.Prime 15373 := by norm_num

private theorem prime_twentySixX_15607 : Nat.Prime 15607 := by norm_num

private theorem prime_twentySixX_16097 : Nat.Prime 16097 := by norm_num

private theorem prime_twentySixX_16763 : Nat.Prime 16763 := by norm_num

private theorem prime_twentySixX_17449 : Nat.Prime 17449 := by norm_num

private theorem prime_twentySixX_18869 : Nat.Prime 18869 := by norm_num

private theorem prime_twentySixX_19387 : Nat.Prime 19387 := by norm_num

private theorem prime_twentySixX_19963 : Nat.Prime 19963 := by norm_num

private theorem prime_twentySixX_20023 : Nat.Prime 20023 := by norm_num

private theorem prime_twentySixX_20029 : Nat.Prime 20029 := by norm_num

private theorem prime_twentySixX_20543 : Nat.Prime 20543 := by norm_num

private theorem prime_twentySixX_20719 : Nat.Prime 20719 := by norm_num

private theorem prime_twentySixX_21569 : Nat.Prime 21569 := by norm_num

private theorem prime_twentySixX_21611 : Nat.Prime 21611 := by norm_num

private theorem prime_twentySixX_21911 : Nat.Prime 21911 := by norm_num

private theorem prime_twentySixX_24019 : Nat.Prime 24019 := by norm_num

private theorem prime_twentySixX_25373 : Nat.Prime 25373 := by norm_num

private theorem prime_twentySixX_25657 : Nat.Prime 25657 := by norm_num

private theorem prime_twentySixX_25951 : Nat.Prime 25951 := by norm_num

private theorem prime_twentySixX_26669 : Nat.Prime 26669 := by norm_num

private theorem prime_twentySixX_27197 : Nat.Prime 27197 := by norm_num

private theorem prime_twentySixX_27509 : Nat.Prime 27509 := by norm_num

private theorem prime_twentySixX_28229 : Nat.Prime 28229 := by norm_num

private theorem prime_twentySixX_28351 : Nat.Prime 28351 := by norm_num

private theorem prime_twentySixX_29879 : Nat.Prime 29879 := by norm_num

private theorem prime_twentySixX_30853 : Nat.Prime 30853 := by norm_num

private theorem prime_twentySixX_31817 : Nat.Prime 31817 := by norm_num

private theorem prime_twentySixX_32029 : Nat.Prime 32029 := by norm_num

private theorem prime_twentySixX_32369 : Nat.Prime 32369 := by norm_num

private theorem prime_twentySixX_32423 : Nat.Prime 32423 := by norm_num

private theorem prime_twentySixX_33049 : Nat.Prime 33049 := by norm_num

private theorem prime_twentySixX_33829 : Nat.Prime 33829 := by norm_num

private theorem prime_twentySixX_35447 : Nat.Prime 35447 := by norm_num

private theorem prime_twentySixX_36263 : Nat.Prime 36263 := by norm_num

private theorem prime_twentySixX_37013 : Nat.Prime 37013 := by norm_num

private theorem prime_twentySixX_39227 : Nat.Prime 39227 := by norm_num

private theorem prime_twentySixX_39581 : Nat.Prime 39581 := by norm_num

private theorem prime_twentySixX_39791 : Nat.Prime 39791 := by norm_num

private theorem prime_twentySixX_41189 : Nat.Prime 41189 := by norm_num

private theorem prime_twentySixX_42181 : Nat.Prime 42181 := by norm_num

private theorem prime_twentySixX_44497 : Nat.Prime 44497 := by norm_num

private theorem prime_twentySixX_44987 : Nat.Prime 44987 := by norm_num

private theorem prime_twentySixX_46861 : Nat.Prime 46861 := by norm_num

private theorem prime_twentySixX_47149 : Nat.Prime 47149 := by norm_num

private theorem prime_twentySixX_49277 : Nat.Prime 49277 := by norm_num

private theorem prime_twentySixX_49409 : Nat.Prime 49409 := by norm_num

private theorem prime_twentySixX_55849 : Nat.Prime 55849 := by norm_num

private theorem prime_twentySixX_62981 : Nat.Prime 62981 := by norm_num

private theorem prime_twentySixX_65713 : Nat.Prime 65713 := by norm_num

private theorem prime_twentySixX_67819 : Nat.Prime 67819 := by norm_num

private theorem prime_twentySixX_71861 : Nat.Prime 71861 := by norm_num

private theorem prime_twentySixX_74323 : Nat.Prime 74323 := by norm_num

private theorem prime_twentySixX_75557 : Nat.Prime 75557 := by norm_num

private theorem prime_twentySixX_76259 : Nat.Prime 76259 := by norm_num

private theorem prime_twentySixX_82261 : Nat.Prime 82261 := by norm_num

private theorem prime_twentySixX_83423 : Nat.Prime 83423 := by norm_num

private theorem prime_twentySixX_83621 : Nat.Prime 83621 := by norm_num

private theorem prime_twentySixX_84017 : Nat.Prime 84017 := by norm_num

private theorem prime_twentySixX_85247 : Nat.Prime 85247 := by norm_num

private theorem prime_twentySixX_85469 : Nat.Prime 85469 := by norm_num

private theorem prime_twentySixX_90107 : Nat.Prime 90107 := by norm_num

private theorem prime_twentySixX_94651 : Nat.Prime 94651 := by norm_num

private theorem prime_twentySixX_95083 : Nat.Prime 95083 := by norm_num

private theorem prime_twentySixX_96211 : Nat.Prime 96211 := by norm_num

private theorem prime_twentySixX_106277 : Nat.Prime 106277 := by norm_num

private theorem prime_twentySixX_111539 : Nat.Prime 111539 := by norm_num

private theorem prime_twentySixX_112741 : Nat.Prime 112741 := by norm_num

private theorem prime_twentySixX_115781 : Nat.Prime 115781 := by norm_num

private theorem prime_twentySixX_118691 : Nat.Prime 118691 := by norm_num

private theorem prime_twentySixX_119653 : Nat.Prime 119653 := by norm_num

private theorem prime_twentySixX_128257 : Nat.Prime 128257 := by norm_num

private theorem prime_twentySixX_139939 : Nat.Prime 139939 := by norm_num

private theorem prime_twentySixX_146173 : Nat.Prime 146173 := by norm_num

private theorem prime_twentySixX_150343 : Nat.Prime 150343 := by norm_num

private theorem prime_twentySixX_150377 : Nat.Prime 150377 := by norm_num

private theorem prime_twentySixX_153929 : Nat.Prime 153929 := by norm_num

private theorem prime_twentySixX_155693 : Nat.Prime 155693 := by norm_num

private theorem prime_twentySixX_158759 : Nat.Prime 158759 := by norm_num

private theorem prime_twentySixX_161717 : Nat.Prime 161717 := by norm_num

private theorem prime_twentySixX_166931 : Nat.Prime 166931 := by norm_num

private theorem prime_twentySixX_167537 : Nat.Prime 167537 := by norm_num

private theorem prime_twentySixX_178261 : Nat.Prime 178261 := by norm_num

private theorem prime_twentySixX_187127 : Nat.Prime 187127 := by norm_num

private theorem prime_twentySixX_199109 : Nat.Prime 199109 := by norm_num

private theorem prime_twentySixX_201167 : Nat.Prime 201167 := by norm_num

private theorem prime_twentySixX_209623 : Nat.Prime 209623 := by norm_num

private theorem prime_twentySixX_227873 : Nat.Prime 227873 := by norm_num

private theorem prime_twentySixX_242257 : Nat.Prime 242257 := by norm_num

private theorem prime_twentySixX_248057 : Nat.Prime 248057 := by norm_num

private theorem prime_twentySixX_249593 : Nat.Prime 249593 := by norm_num

private theorem prime_twentySixX_254927 : Nat.Prime 254927 := by norm_num

private theorem prime_twentySixX_256889 : Nat.Prime 256889 := by norm_num

private theorem prime_twentySixX_259213 : Nat.Prime 259213 := by norm_num

private theorem prime_twentySixX_265247 : Nat.Prime 265247 := by norm_num

private theorem prime_twentySixX_270563 : Nat.Prime 270563 := by norm_num

private theorem prime_twentySixX_274831 : Nat.Prime 274831 := by norm_num

private theorem prime_twentySixX_278911 : Nat.Prime 278911 := by norm_num

private theorem prime_twentySixX_318313 : Nat.Prime 318313 := by norm_num

private theorem prime_twentySixX_335009 : Nat.Prime 335009 := by norm_num

private theorem prime_twentySixX_391873 : Nat.Prime 391873 := by norm_num

private theorem prime_twentySixX_392099 : Nat.Prime 392099 := by norm_num

private theorem prime_twentySixX_409901 : Nat.Prime 409901 := by norm_num

private theorem prime_twentySixX_413141 : Nat.Prime 413141 := by norm_num

private theorem prime_twentySixX_421133 : Nat.Prime 421133 := by norm_num

private theorem prime_twentySixX_480379 : Nat.Prime 480379 := by norm_num

private theorem prime_twentySixX_524453 : Nat.Prime 524453 := by norm_num

private theorem prime_twentySixX_556859 : Nat.Prime 556859 := by norm_num

private theorem prime_twentySixX_558979 : Nat.Prime 558979 := by norm_num

private theorem prime_twentySixX_576523 : Nat.Prime 576523 := by norm_num

private theorem prime_twentySixX_590437 : Nat.Prime 590437 := by norm_num

private theorem prime_twentySixX_642871 : Nat.Prime 642871 := by norm_num

private theorem prime_twentySixX_657653 : Nat.Prime 657653 := by norm_num

private theorem prime_twentySixX_663203 : Nat.Prime 663203 := by norm_num

private theorem prime_twentySixX_667123 : Nat.Prime 667123 := by norm_num

private theorem prime_twentySixX_714283 : Nat.Prime 714283 := by norm_num

private theorem prime_twentySixX_759313 : Nat.Prime 759313 := by norm_num

private theorem prime_twentySixX_763739 : Nat.Prime 763739 := by norm_num

private theorem prime_twentySixX_796583 : Nat.Prime 796583 := by norm_num

private theorem prime_twentySixX_797947 : Nat.Prime 797947 := by norm_num

private theorem prime_twentySixX_813107 : Nat.Prime 813107 := by norm_num

private theorem prime_twentySixX_830899 : Nat.Prime 830899 := by norm_num

private theorem prime_twentySixX_852559 : Nat.Prime 852559 := by norm_num

private theorem prime_twentySixX_873139 : Nat.Prime 873139 := by norm_num

private theorem prime_twentySixX_893041 : Nat.Prime 893041 := by norm_num

private theorem prime_twentySixX_897517 : Nat.Prime 897517 := by norm_num

private theorem prime_twentySixX_936917 : Nat.Prime 936917 := by norm_num

private theorem prime_twentySixX_955337 : Nat.Prime 955337 := by norm_num

private theorem prime_twentySixX_991073 : Nat.Prime 991073 := by norm_num

private theorem prime_twentySixX_995117 : Nat.Prime 995117 := by norm_num

private theorem prime_twentySixX_1029563 : Nat.Prime 1029563 := by norm_num

private theorem prime_twentySixX_1053739 : Nat.Prime 1053739 := by norm_num

private theorem prime_twentySixX_1086611 : Nat.Prime 1086611 := by norm_num

private theorem prime_twentySixX_1093943 : Nat.Prime 1093943 := by norm_num

private theorem prime_twentySixX_1110271 : Nat.Prime 1110271 := by norm_num

private theorem prime_twentySixX_1125419 : Nat.Prime 1125419 := by norm_num

private theorem prime_twentySixX_1140949 : Nat.Prime 1140949 := by norm_num

private theorem prime_twentySixX_1194601 : Nat.Prime 1194601 := by norm_num

private theorem prime_twentySixX_1219613 : Nat.Prime 1219613 := by norm_num

private theorem prime_twentySixX_1222931 : Nat.Prime 1222931 := by norm_num

private theorem prime_twentySixX_1243969 : Nat.Prime 1243969 := by norm_num

private theorem prime_twentySixX_1249627 : Nat.Prime 1249627 := by norm_num

private theorem prime_twentySixX_1285429 : Nat.Prime 1285429 := by norm_num

private theorem prime_twentySixX_1288247 : Nat.Prime 1288247 := by norm_num

private theorem prime_twentySixX_1292293 : Nat.Prime 1292293 := by norm_num

private theorem prime_twentySixX_1296293 : Nat.Prime 1296293 := by norm_num

private theorem prime_twentySixX_1430543 : Nat.Prime 1430543 := by norm_num

private theorem prime_twentySixX_1500157 : Nat.Prime 1500157 := by norm_num

private theorem prime_twentySixX_1582963 : Nat.Prime 1582963 := by norm_num

private theorem prime_twentySixX_1584001 : Nat.Prime 1584001 := by norm_num

private theorem prime_twentySixX_1628203 : Nat.Prime 1628203 := by norm_num

private theorem prime_twentySixX_1659491 : Nat.Prime 1659491 := by norm_num

private theorem prime_twentySixX_1874699 : Nat.Prime 1874699 := by norm_num

private theorem prime_twentySixX_1919789 : Nat.Prime 1919789 := by norm_num

private theorem prime_twentySixX_1921687 : Nat.Prime 1921687 := by norm_num

private theorem prime_twentySixX_2144047 : Nat.Prime 2144047 := by norm_num

private theorem prime_twentySixX_2220277 : Nat.Prime 2220277 := by norm_num

private theorem prime_twentySixX_2273119 : Nat.Prime 2273119 := by norm_num

private theorem prime_twentySixX_2309477 : Nat.Prime 2309477 := by norm_num

private theorem prime_twentySixX_2388583 : Nat.Prime 2388583 := by norm_num

private theorem prime_twentySixX_2596501 : Nat.Prime 2596501 := by norm_num

private theorem prime_twentySixX_2613139 : Nat.Prime 2613139 := by norm_num

private theorem prime_twentySixX_2795069 : Nat.Prime 2795069 := by norm_num

private theorem prime_twentySixX_2799187 : Nat.Prime 2799187 := by norm_num

private theorem prime_twentySixX_3011117 : Nat.Prime 3011117 := by norm_num

private theorem prime_twentySixX_3089857 : Nat.Prime 3089857 := by norm_num

private theorem prime_twentySixX_3225139 : Nat.Prime 3225139 := by norm_num

private theorem prime_twentySixX_3268163 : Nat.Prime 3268163 := by norm_num

private theorem prime_twentySixX_3279559 : Nat.Prime 3279559 := by norm_num

private theorem prime_twentySixX_3399569 : Nat.Prime 3399569 := by norm_num

private theorem prime_twentySixX_3479089 : Nat.Prime 3479089 := by norm_num

private theorem prime_twentySixX_3720487 : Nat.Prime 3720487 := by norm_num

private theorem prime_twentySixX_3989119 : Nat.Prime 3989119 := by norm_num

private theorem prime_twentySixX_4391371 : Nat.Prime 4391371 := by norm_num

private theorem prime_twentySixX_4553573 : Nat.Prime 4553573 := by norm_num

private theorem prime_twentySixX_4584841 : Nat.Prime 4584841 := by norm_num

private theorem prime_twentySixX_5027959 : Nat.Prime 5027959 := by norm_num

private theorem prime_twentySixX_5082277 : Nat.Prime 5082277 := by norm_num

private theorem prime_twentySixX_5140117 : Nat.Prime 5140117 := by norm_num

private theorem prime_twentySixX_5309207 : Nat.Prime 5309207 := by norm_num

private theorem prime_twentySixX_5340763 : Nat.Prime 5340763 := by norm_num

private theorem prime_twentySixX_5534623 : Nat.Prime 5534623 := by norm_num

private theorem prime_twentySixX_5591029 : Nat.Prime 5591029 := by norm_num

private theorem prime_twentySixX_6295841 : Nat.Prime 6295841 := by norm_num

private theorem prime_twentySixX_6976699 : Nat.Prime 6976699 := by norm_num

private theorem prime_twentySixX_7590001 : Nat.Prime 7590001 := by norm_num

private theorem prime_twentySixX_7595443 : Nat.Prime 7595443 := by norm_num

private theorem prime_twentySixX_8270923 : Nat.Prime 8270923 := by norm_num

private theorem prime_twentySixX_8429209 : Nat.Prime 8429209 := by norm_num

private theorem prime_twentySixX_8485579 : Nat.Prime 8485579 := by norm_num

private theorem prime_twentySixX_8562377 : Nat.Prime 8562377 := by norm_num

private theorem prime_twentySixX_8563067 : Nat.Prime 8563067 := by norm_num

private theorem prime_twentySixX_9269333 : Nat.Prime 9269333 := by norm_num

private theorem prime_twentySixX_9441539 : Nat.Prime 9441539 := by norm_num

private theorem prime_twentySixX_9445537 : Nat.Prime 9445537 := by norm_num

private theorem prime_twentySixX_10537391 : Nat.Prime 10537391 := by
  apply lucas_primality 10537391 (7 : ZMod 10537391)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1053739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1053739, 1)] : List FactorBlock).map factorBlockValue).prod) = 10537391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_1053739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10537391) ^ 5268695 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10537391) ^ 2107478 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10537391) ^ 10 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_10801067 : Nat.Prime 10801067 := by
  apply lucas_primality 10801067 (2 : ZMod 10801067)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (859, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (859, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) = 10801067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_859
      · exact prime_twentySixX_6287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10801067) ^ 5400533 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10801067) ^ 12574 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 10801067) ^ 1718 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_13116839 : Nat.Prime 13116839 := by
  apply lucas_primality 13116839 (7 : ZMod 13116839)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (936917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (936917, 1)] : List FactorBlock).map factorBlockValue).prod) = 13116839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_936917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 13116839) ^ 6558419 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13116839) ^ 1873834 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13116839) ^ 14 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_13875023 : Nat.Prime 13875023 := by
  apply lucas_primality 13875023 (5 : ZMod 13875023)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (991073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (991073, 1)] : List FactorBlock).map factorBlockValue).prod) = 13875023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_991073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13875023) ^ 6937511 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13875023) ^ 1982146 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13875023) ^ 14 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_14457413 : Nat.Prime 14457413 := by
  apply lucas_primality 14457413 (2 : ZMod 14457413)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (107, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (107, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) = 14457413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_107
      · exact prime_twentySixX_1987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14457413) ^ 7228706 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14457413) ^ 850436 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14457413) ^ 135116 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14457413) ^ 7276 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_16142521 : Nat.Prime 16142521 := by
  apply lucas_primality 16142521 (7 : ZMod 16142521)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 16142521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_t64_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16142521) ^ 8071260 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16142521) ^ 5380840 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16142521) ^ 3228504 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16142521) ^ 949560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16142521) ^ 393720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16142521) ^ 83640 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18292397 : Nat.Prime 18292397 := by
  apply lucas_primality 18292397 (2 : ZMod 18292397)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (111539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (111539, 1)] : List FactorBlock).map factorBlockValue).prod) = 18292397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_twentySixX_111539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18292397) ^ 9146198 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18292397) ^ 446156 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18292397) ^ 164 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18566963 : Nat.Prime 18566963 := by
  apply lucas_primality 18566963 (2 : ZMod 18566963)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1471, 1), (6311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1471, 1), (6311, 1)] : List FactorBlock).map factorBlockValue).prod) = 18566963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_1471
      · exact prime_twentySixX_6311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18566963) ^ 9283481 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18566963) ^ 12622 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18566963) ^ 2942 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18915877 : Nat.Prime 18915877 := by
  apply lucas_primality 18915877 (5 : ZMod 18915877)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (131, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (131, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 18915877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentySixX_131
      · exact prime_t64_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18915877) ^ 9457938 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18915877) ^ 6305292 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18915877) ^ 2702268 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18915877) ^ 144396 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18915877) ^ 99036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_22420633 : Nat.Prime 22420633 := by
  apply lucas_primality 22420633 (5 : ZMod 22420633)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (71861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (71861, 1)] : List FactorBlock).map factorBlockValue).prod) = 22420633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentySixX_71861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22420633) ^ 11210316 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22420633) ^ 7473544 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22420633) ^ 1724664 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 22420633) ^ 312 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_22724479 : Nat.Prime 22724479 := by
  apply lucas_primality 22724479 (6 : ZMod 22724479)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (103, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (103, 2)] : List FactorBlock).map factorBlockValue).prod) = 22724479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22724479) ^ 11362239 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 22724479) ^ 7574826 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 22724479) ^ 3246354 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 22724479) ^ 1336734 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 22724479) ^ 220626 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_23213591 : Nat.Prime 23213591 := by
  apply lucas_primality 23213591 (7 : ZMod 23213591)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) = 23213591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_113
      · exact prime_twentySixX_20543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23213591) ^ 11606795 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23213591) ^ 4642718 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23213591) ^ 205430 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 23213591) ^ 1130 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_23329171 : Nat.Prime 23329171 := by
  apply lucas_primality 23329171 (2 : ZMod 23329171)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (259213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (259213, 1)] : List FactorBlock).map factorBlockValue).prod) = 23329171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_259213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23329171) ^ 11664585 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23329171) ^ 7776390 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23329171) ^ 4665834 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23329171) ^ 90 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_26281223 : Nat.Prime 26281223 := by
  apply lucas_primality 26281223 (5 : ZMod 26281223)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1194601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1194601, 1)] : List FactorBlock).map factorBlockValue).prod) = 26281223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentySixX_1194601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26281223) ^ 13140611 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26281223) ^ 2389202 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 26281223) ^ 22 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_26828093 : Nat.Prime 26828093 := by
  apply lucas_primality 26828093 (2 : ZMod 26828093)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1459, 1), (4597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1459, 1), (4597, 1)] : List FactorBlock).map factorBlockValue).prod) = 26828093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_1459
      · exact prime_twentySixX_4597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26828093) ^ 13414046 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26828093) ^ 18388 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26828093) ^ 5836 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_27509047 : Nat.Prime 27509047 := by
  apply lucas_primality 27509047 (3 : ZMod 27509047)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4584841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4584841, 1)] : List FactorBlock).map factorBlockValue).prod) = 27509047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_4584841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27509047) ^ 13754523 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27509047) ^ 9169682 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 27509047) ^ 6 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_29270713 : Nat.Prime 29270713 := by
  apply lucas_primality 29270713 (5 : ZMod 29270713)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1219613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1219613, 1)] : List FactorBlock).map factorBlockValue).prod) = 29270713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_1219613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 29270713) ^ 14635356 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 29270713) ^ 9756904 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 29270713) ^ 24 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_31784387 : Nat.Prime 31784387 := by
  apply lucas_primality 31784387 (2 : ZMod 31784387)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (201167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (201167, 1)] : List FactorBlock).map factorBlockValue).prod) = 31784387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_twentySixX_201167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31784387) ^ 15892193 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784387) ^ 402334 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784387) ^ 158 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_31813867 : Nat.Prime 31813867 := by
  apply lucas_primality 31813867 (5 : ZMod 31813867)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (97, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (97, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 31813867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_97
      · exact prime_t64_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31813867) ^ 15906933 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813867) ^ 10604622 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813867) ^ 4544838 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813867) ^ 1674414 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813867) ^ 327978 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 31813867) ^ 232218 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_32123629 : Nat.Prime 32123629 := by
  apply lucas_primality 32123629 (2 : ZMod 32123629)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (33049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (33049, 1)] : List FactorBlock).map factorBlockValue).prod) = 32123629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_33049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32123629) ^ 16061814 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32123629) ^ 10707876 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32123629) ^ 972 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_32251391 : Nat.Prime 32251391 := by
  apply lucas_primality 32251391 (7 : ZMod 32251391)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3225139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3225139, 1)] : List FactorBlock).map factorBlockValue).prod) = 32251391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_3225139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 32251391) ^ 16125695 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 32251391) ^ 6450278 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 32251391) ^ 10 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_33942317 : Nat.Prime 33942317 := by
  apply lucas_primality 33942317 (2 : ZMod 33942317)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8485579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8485579, 1)] : List FactorBlock).map factorBlockValue).prod) = 33942317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_8485579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33942317) ^ 16971158 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 33942317) ^ 4 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_35160511 : Nat.Prime 35160511 := by
  apply lucas_primality 35160511 (3 : ZMod 35160511)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 35160511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_31
      · exact prime_t64_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35160511) ^ 17580255 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 11720170 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 7032102 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 5022930 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 3196410 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 1134210 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35160511) ^ 71610 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_37133927 : Nat.Prime 37133927 := by
  apply lucas_primality 37133927 (5 : ZMod 37133927)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18566963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18566963, 1)] : List FactorBlock).map factorBlockValue).prod) = 37133927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_18566963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 37133927) ^ 18566963 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37133927) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_39198199 : Nat.Prime 39198199 := by
  apply lucas_primality 39198199 (6 : ZMod 39198199)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 39198199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_43
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39198199) ^ 19599099 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 13066066 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 3015246 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1351662 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1264458 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 911586 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_39354709 : Nat.Prime 39354709 := by
  apply lucas_primality 39354709 (2 : ZMod 39354709)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3279559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3279559, 1)] : List FactorBlock).map factorBlockValue).prod) = 39354709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_3279559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39354709) ^ 19677354 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39354709) ^ 13118236 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39354709) ^ 12 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_39891191 : Nat.Prime 39891191 := by
  apply lucas_primality 39891191 (7 : ZMod 39891191)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3989119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3989119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39891191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_3989119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 39891191) ^ 19945595 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39891191) ^ 7978238 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 39891191) ^ 10 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_42426119 : Nat.Prime 42426119 := by
  apply lucas_primality 42426119 (7 : ZMod 42426119)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (178261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (178261, 1)] : List FactorBlock).map factorBlockValue).prod) = 42426119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_twentySixX_178261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42426119) ^ 21213059 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 42426119) ^ 6060874 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 42426119) ^ 2495654 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 42426119) ^ 238 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_44868547 : Nat.Prime 44868547 := by
  apply lucas_primality 44868547 (2 : ZMod 44868547)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (830899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (830899, 1)] : List FactorBlock).map factorBlockValue).prod) = 44868547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_830899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44868547) ^ 22434273 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868547) ^ 14956182 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868547) ^ 54 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_46053307 : Nat.Prime 46053307 := by
  apply lucas_primality 46053307 (2 : ZMod 46053307)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 46053307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46053307) ^ 23026653 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 15351102 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 3542562 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 2709018 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 202878 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_46471379 : Nat.Prime 46471379 := by
  apply lucas_primality 46471379 (2 : ZMod 46471379)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1222931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1222931, 1)] : List FactorBlock).map factorBlockValue).prod) = 46471379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentySixX_1222931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46471379) ^ 23235689 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46471379) ^ 2445862 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46471379) ^ 38 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_55275637 : Nat.Prime 55275637 := by
  apply lucas_primality 55275637 (2 : ZMod 55275637)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (19, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (19, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 55275637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_twentySixX_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55275637) ^ 27637818 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 55275637) ^ 18425212 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 55275637) ^ 4251972 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 55275637) ^ 3251508 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 55275637) ^ 2909244 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 55275637) ^ 50388 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_58233559 : Nat.Prime 58233559 := by
  apply lucas_primality 58233559 (6 : ZMod 58233559)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1933, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1933, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 58233559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_1933
      · exact prime_twentySixX_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 58233559) ^ 29116779 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 19411186 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 30126 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 11598 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_59566873 : Nat.Prime 59566873 := by
  apply lucas_primality 59566873 (5 : ZMod 59566873)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (31, 1), (59, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (31, 1), (59, 2)] : List FactorBlock).map factorBlockValue).prod) = 59566873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_t64_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 59566873) ^ 29783436 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59566873) ^ 19855624 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59566873) ^ 2589864 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59566873) ^ 1921512 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 59566873) ^ 1009608 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_60064987 : Nat.Prime 60064987 := by
  apply lucas_primality 60064987 (3 : ZMod 60064987)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (270563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (270563, 1)] : List FactorBlock).map factorBlockValue).prod) = 60064987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_twentySixX_270563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60064987) ^ 30032493 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 20021662 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 1623378 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 222 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_63416971 : Nat.Prime 63416971 := by
  apply lucas_primality 63416971 (2 : ZMod 63416971)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (181, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (181, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 63416971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_twentySixX_181
      · exact prime_t64_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63416971) ^ 31708485 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 21138990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 12683394 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 3730410 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 350370 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 276930 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_64502783 : Nat.Prime 64502783 := by
  apply lucas_primality 64502783 (5 : ZMod 64502783)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32251391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32251391, 1)] : List FactorBlock).map factorBlockValue).prod) = 64502783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_32251391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64502783) ^ 32251391 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 64502783) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_68392019 : Nat.Prime 68392019 := by
  apply lucas_primality 68392019 (2 : ZMod 68392019)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) = 68392019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_t64_41
      · exact prime_twentySixX_36263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68392019) ^ 34196009 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 2973566 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1668098 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1886 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_79782383 : Nat.Prime 79782383 := by
  apply lucas_primality 79782383 (5 : ZMod 79782383)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39891191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39891191, 1)] : List FactorBlock).map factorBlockValue).prod) = 79782383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_39891191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 79782383) ^ 39891191 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 79782383) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_80219981 : Nat.Prime 80219981 := by
  apply lucas_primality 80219981 (2 : ZMod 80219981)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) = 80219981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_257
      · exact prime_twentySixX_15607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80219981) ^ 40109990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 16043996 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 312140 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 5140 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_83511149 : Nat.Prime 83511149 := by
  apply lucas_primality 83511149 (2 : ZMod 83511149)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) = 83511149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_twentySixX_96211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83511149) ^ 41755574 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 11930164 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 2693908 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_90218467 : Nat.Prime 90218467 := by
  apply lucas_primality 90218467 (2 : ZMod 90218467)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (23, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (23, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) = 90218467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_twentySixX_16763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90218467) ^ 45109233 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 30072822 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 6939882 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 3922542 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 5382 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_109978417 : Nat.Prime 109978417 := by
  apply lucas_primality 109978417 (5 : ZMod 109978417)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (763739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (763739, 1)] : List FactorBlock).map factorBlockValue).prod) = 109978417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_763739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 109978417) ^ 54989208 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 109978417) ^ 36659472 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 109978417) ^ 144 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_118535279 : Nat.Prime 118535279 := by
  apply lucas_primality 118535279 (7 : ZMod 118535279)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1831, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1831, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) = 118535279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_1831
      · exact prime_twentySixX_32369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 118535279) ^ 59267639 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 118535279) ^ 64738 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 118535279) ^ 3662 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_120491003 : Nat.Prime 120491003 := by
  apply lucas_primality 120491003 (2 : ZMod 120491003)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1663, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1663, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 120491003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentySixX_1663
      · exact prime_twentySixX_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120491003) ^ 60245501 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 7087706 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 72454 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 120491003) ^ 56542 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_148272073 : Nat.Prime 148272073 := by
  apply lucas_primality 148272073 (5 : ZMod 148272073)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 148272073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_t64_67
      · exact prime_twentySixX_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 148272073) ^ 74136036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 49424024 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 11405544 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 3616392 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 2213016 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 857064 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_158288029 : Nat.Prime 158288029 := by
  apply lucas_primality 158288029 (6 : ZMod 158288029)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) = 158288029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_157
      · exact prime_twentySixX_84017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 158288029) ^ 79144014 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 52762676 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1008204 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1884 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_160439963 : Nat.Prime 160439963 := by
  apply lucas_primality 160439963 (2 : ZMod 160439963)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) = 160439963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_80219981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160439963) ^ 80219981 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160439963) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_164681581 : Nat.Prime 164681581 := by
  apply lucas_primality 164681581 (10 : ZMod 164681581)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) = 164681581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentySixX_392099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 164681581) ^ 82340790 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 54893860 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 32936316 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 23525940 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 420 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_168197789 : Nat.Prime 168197789 := by
  apply lucas_primality 168197789 (2 : ZMod 168197789)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) = 168197789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_113
      · exact prime_twentySixX_33829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168197789) ^ 84098894 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 15290708 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 1488476 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 4972 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_179474189 : Nat.Prime 179474189 := by
  apply lucas_primality 179474189 (2 : ZMod 179474189)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (44868547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (44868547, 1)] : List FactorBlock).map factorBlockValue).prod) = 179474189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_44868547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 179474189) ^ 89737094 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 179474189) ^ 4 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_189673039 : Nat.Prime 189673039 := by
  apply lucas_primality 189673039 (3 : ZMod 189673039)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) = 189673039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_10537391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 189673039) ^ 94836519 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 63224346 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 18 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_200438423 : Nat.Prime 200438423 := by
  apply lucas_primality 200438423 (10 : ZMod 200438423)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (106277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (106277, 1)] : List FactorBlock).map factorBlockValue).prod) = 200438423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_t64_41
      · exact prime_twentySixX_106277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 200438423) ^ 100219211 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 8714714 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 4888742 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 200438423) ^ 1886 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_210138469 : Nat.Prime 210138469 := by
  apply lucas_primality 210138469 (6 : ZMod 210138469)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3547, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3547, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 210138469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_3547
      · exact prime_twentySixX_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 210138469) ^ 105069234 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 70046156 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 59244 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 210138469) ^ 42564 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_220118471 : Nat.Prime 220118471 := by
  apply lucas_primality 220118471 (11 : ZMod 220118471)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) = 220118471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentySixX_153929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220118471) ^ 110059235 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 44023694 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 20010770 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 16932190 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 1430 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_222398269 : Nat.Prime 222398269 := by
  apply lucas_primality 222398269 (2 : ZMod 222398269)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (37, 1), (41, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (37, 1), (41, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 222398269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_twentySixX_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 222398269) ^ 111199134 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 222398269) ^ 74132756 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 222398269) ^ 11705172 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 222398269) ^ 6010764 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 222398269) ^ 5424348 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 222398269) ^ 345876 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_237317393 : Nat.Prime 237317393 := by
  apply lucas_primality 237317393 (3 : ZMod 237317393)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1140949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1140949, 1)] : List FactorBlock).map factorBlockValue).prod) = 237317393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_1140949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 237317393) ^ 118658696 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 237317393) ^ 18255184 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 237317393) ^ 208 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_240259949 : Nat.Prime 240259949 := by
  apply lucas_primality 240259949 (2 : ZMod 240259949)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (60064987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (60064987, 1)] : List FactorBlock).map factorBlockValue).prod) = 240259949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_60064987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 240259949) ^ 120129974 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 240259949) ^ 4 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_243182789 : Nat.Prime 243182789 := by
  apply lucas_primality 243182789 (2 : ZMod 243182789)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7013, 1), (8669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7013, 1), (8669, 1)] : List FactorBlock).map factorBlockValue).prod) = 243182789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_7013
      · exact prime_twentySixX_8669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 243182789) ^ 121591394 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243182789) ^ 34676 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243182789) ^ 28052 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_285913427 : Nat.Prime 285913427 := by
  apply lucas_primality 285913427 (2 : ZMod 285913427)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (347, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (347, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) = 285913427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_101
      · exact prime_twentySixX_347
      · exact prime_twentySixX_4079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 285913427) ^ 142956713 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 285913427) ^ 2830826 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 285913427) ^ 823958 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 285913427) ^ 70094 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_297071417 : Nat.Prime 297071417 := by
  apply lucas_primality 297071417 (3 : ZMod 297071417)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37133927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37133927, 1)] : List FactorBlock).map factorBlockValue).prod) = 297071417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_37133927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 297071417) ^ 148535708 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 297071417) ^ 8 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_320879927 : Nat.Prime 320879927 := by
  apply lucas_primality 320879927 (5 : ZMod 320879927)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) = 320879927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_160439963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 320879927) ^ 160439963 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 320879927) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_336079223 : Nat.Prime 336079223 := by
  apply lucas_primality 336079223 (5 : ZMod 336079223)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (167537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (167537, 1)] : List FactorBlock).map factorBlockValue).prod) = 336079223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_59
      · exact prime_twentySixX_167537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 336079223) ^ 168039611 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 336079223) ^ 19769366 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 336079223) ^ 5696258 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 336079223) ^ 2006 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_358530919 : Nat.Prime 358530919 := by
  apply lucas_primality 358530919 (6 : ZMod 358530919)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (137, 1), (25657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (137, 1), (25657, 1)] : List FactorBlock).map factorBlockValue).prod) = 358530919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_137
      · exact prime_twentySixX_25657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 358530919) ^ 179265459 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 358530919) ^ 119510306 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 358530919) ^ 21090054 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 358530919) ^ 2617014 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 358530919) ^ 13974 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_358948379 : Nat.Prime 358948379 := by
  apply lucas_primality 358948379 (2 : ZMod 358948379)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179474189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179474189, 1)] : List FactorBlock).map factorBlockValue).prod) = 358948379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_179474189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 358948379) ^ 179474189 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 358948379) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_360347051 : Nat.Prime 360347051 := by
  apply lucas_primality 360347051 (2 : ZMod 360347051)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) = 360347051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentySixX_1029563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 360347051) ^ 180173525 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 72069410 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 51478150 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 350 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_429845593 : Nat.Prime 429845593 := by
  apply lucas_primality 429845593 (5 : ZMod 429845593)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) = 429845593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentySixX_1628203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 429845593) ^ 214922796 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 143281864 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 39076872 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 264 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_432370943 : Nat.Prime 432370943 := by
  apply lucas_primality 432370943 (5 : ZMod 432370943)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (1249627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (1249627, 1)] : List FactorBlock).map factorBlockValue).prod) = 432370943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_173
      · exact prime_twentySixX_1249627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 432370943) ^ 216185471 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 432370943) ^ 2499254 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 432370943) ^ 346 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_440144753 : Nat.Prime 440144753 := by
  apply lucas_primality 440144753 (3 : ZMod 440144753)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) = 440144753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_27509047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 440144753) ^ 220072376 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 440144753) ^ 16 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_456068273 : Nat.Prime 456068273 := by
  apply lucas_primality 456068273 (3 : ZMod 456068273)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (191, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) = 456068273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_191
      · exact prime_twentySixX_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456068273) ^ 228034136 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 41460752 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 2387792 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 456068273) ^ 33616 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_477151799 : Nat.Prime 477151799 := by
  apply lucas_primality 477151799 (11 : ZMod 477151799)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (3268163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (3268163, 1)] : List FactorBlock).map factorBlockValue).prod) = 477151799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_73
      · exact prime_twentySixX_3268163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 477151799) ^ 238575899 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 477151799) ^ 6536326 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 477151799) ^ 146 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_508736671 : Nat.Prime 508736671 := by
  apply lucas_primality 508736671 (3 : ZMod 508736671)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (401, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (401, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 508736671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentySixX_401
      · exact prime_twentySixX_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 508736671) ^ 254368335 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 169578890 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 101747334 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 39133590 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 1268670 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 508736671) ^ 156390 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_567322361 : Nat.Prime 567322361 := by
  apply lucas_primality 567322361 (3 : ZMod 567322361)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (29, 1), (173, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (29, 1), (173, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 567322361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_29
      · exact prime_twentySixX_173
      · exact prime_twentySixX_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 567322361) ^ 283661180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 567322361) ^ 113464472 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 567322361) ^ 51574760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 567322361) ^ 19562840 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 567322361) ^ 3279320 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 567322361) ^ 2207480 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_653634671 : Nat.Prime 653634671 := by
  apply lucas_primality 653634671 (14 : ZMod 653634671)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (5027959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (5027959, 1)] : List FactorBlock).map factorBlockValue).prod) = 653634671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentySixX_5027959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 653634671) ^ 326817335 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 653634671) ^ 130726934 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 653634671) ^ 50279590 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 653634671) ^ 130 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_693751151 : Nat.Prime 693751151 := by
  apply lucas_primality 693751151 (7 : ZMod 693751151)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13875023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13875023, 1)] : List FactorBlock).map factorBlockValue).prod) = 693751151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_13875023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 693751151) ^ 346875575 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 693751151) ^ 138750230 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 693751151) ^ 50 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_752335981 : Nat.Prime 752335981 := by
  apply lucas_primality 752335981 (6 : ZMod 752335981)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 752335981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_twentySixX_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 752335981) ^ 376167990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 250778660 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 150467196 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 68394180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 32710260 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 25942620 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 440220 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_758692157 : Nat.Prime 758692157 := by
  apply lucas_primality 758692157 (2 : ZMod 758692157)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) = 758692157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_189673039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 758692157) ^ 379346078 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 758692157) ^ 4 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_773531243 : Nat.Prime 773531243 := by
  apply lucas_primality 773531243 (2 : ZMod 773531243)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (35160511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (35160511, 1)] : List FactorBlock).map factorBlockValue).prod) = 773531243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentySixX_35160511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 773531243) ^ 386765621 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 773531243) ^ 70321022 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 773531243) ^ 22 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_864741887 : Nat.Prime 864741887 := by
  apply lucas_primality 864741887 (5 : ZMod 864741887)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (432370943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (432370943, 1)] : List FactorBlock).map factorBlockValue).prod) = 864741887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_432370943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 864741887) ^ 432370943 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 864741887) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_954303599 : Nat.Prime 954303599 := by
  apply lucas_primality 954303599 (7 : ZMod 954303599)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (477151799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (477151799, 1)] : List FactorBlock).map factorBlockValue).prod) = 954303599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_477151799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 954303599) ^ 477151799 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 954303599) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1160494157 : Nat.Prime 1160494157 := by
  apply lucas_primality 1160494157 (2 : ZMod 1160494157)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160494157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_521
      · exact prime_twentySixX_556859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1160494157) ^ 580247078 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2227436 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2084 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1194121493 : Nat.Prime 1194121493 := by
  apply lucas_primality 1194121493 (2 : ZMod 1194121493)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6709, 1), (44497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6709, 1), (44497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1194121493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_6709
      · exact prime_twentySixX_44497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1194121493) ^ 597060746 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1194121493) ^ 177988 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1194121493) ^ 26836 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1317915923 : Nat.Prime 1317915923 := by
  apply lucas_primality 1317915923 (2 : ZMod 1317915923)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317915923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_59
      · exact prime_twentySixX_313
      · exact prime_twentySixX_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1317915923) ^ 658957961 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 77524466 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 22337558 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 4210594 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 627878 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1474306679 : Nat.Prime 1474306679 := by
  apply lucas_primality 1474306679 (17 : ZMod 1474306679)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474306679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_127
      · exact prime_twentySixX_457
      · exact prime_twentySixX_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1474306679) ^ 737153339 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 113408206 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 11608714 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 3226054 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 1509014 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1518372857 : Nat.Prime 1518372857 := by
  apply lucas_primality 1518372857 (5 : ZMod 1518372857)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 3), (13, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 3), (13, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1518372857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentySixX_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1518372857) ^ 759186428 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 216910408 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 138033896 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 116797912 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1518372857) ^ 968968 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1561368569 : Nat.Prime 1561368569 := by
  apply lucas_primality 1561368569 (3 : ZMod 1561368569)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (6295841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (6295841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561368569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_twentySixX_6295841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1561368569) ^ 780684284 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561368569) ^ 50366728 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561368569) ^ 248 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1595647661 : Nat.Prime 1595647661 := by
  apply lucas_primality 1595647661 (2 : ZMod 1595647661)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79782383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79782383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1595647661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_79782383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1595647661) ^ 797823830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595647661) ^ 319129532 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595647661) ^ 20 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1855533307 : Nat.Prime 1855533307 := by
  apply lucas_primality 1855533307 (2 : ZMod 1855533307)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (150343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (150343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1855533307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_twentySixX_150343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1855533307) ^ 927766653 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 618511102 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 168684846 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 109149018 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1855533307) ^ 12342 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1908980081 : Nat.Prime 1908980081 := by
  apply lucas_primality 1908980081 (3 : ZMod 1908980081)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (67, 1), (83, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (67, 1), (83, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908980081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_67
      · exact prime_t64_83
      · exact prime_twentySixX_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1908980081) ^ 954490040 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 381796016 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 272711440 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 28492240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 22999760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908980081) ^ 3114160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4499780951 : Nat.Prime 4499780951 := by
  apply lucas_primality 4499780951 (7 : ZMod 4499780951)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4499780951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_twentySixX_558979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4499780951) ^ 2249890475 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 899956190 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 642825850 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 195642650 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 8050 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4509209899 : Nat.Prime 4509209899 := by
  apply lucas_primality 4509209899 (2 : ZMod 4509209899)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5167, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5167, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) = 4509209899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_5167
      · exact prime_twentySixX_5387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4509209899) ^ 2254604949 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4509209899) ^ 1503069966 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4509209899) ^ 872694 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4509209899) ^ 837054 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4598633189 : Nat.Prime 4598633189 := by
  apply lucas_primality 4598633189 (2 : ZMod 4598633189)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4598633189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_twentySixX_8270923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4598633189) ^ 2299316594 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 33083692 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 556 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5025277307 : Nat.Prime 5025277307 := by
  apply lucas_primality 5025277307 (2 : ZMod 5025277307)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (358948379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (358948379, 1)] : List FactorBlock).map factorBlockValue).prod) = 5025277307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_358948379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5025277307) ^ 2512638653 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5025277307) ^ 717896758 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5025277307) ^ 14 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5327453741 : Nat.Prime 5327453741 := by
  apply lucas_primality 5327453741 (2 : ZMod 5327453741)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5327453741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_499
      · exact prime_twentySixX_76259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5327453741) ^ 2663726870 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 1065490748 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 761064820 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 10676260 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 69860 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5834431507 : Nat.Prime 5834431507 := by
  apply lucas_primality 5834431507 (2 : ZMod 5834431507)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5834431507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_twentySixX_26281223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5834431507) ^ 2917215753 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 1944810502 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 157687338 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 222 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6856603493 : Nat.Prime 6856603493 := by
  apply lucas_primality 6856603493 (2 : ZMod 6856603493)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (90218467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (90218467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6856603493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentySixX_90218467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6856603493) ^ 3428301746 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856603493) ^ 360873868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856603493) ^ 76 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6910156909 : Nat.Prime 6910156909 := by
  apply lucas_primality 6910156909 (2 : ZMod 6910156909)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149, 1), (1288247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149, 1), (1288247, 1)] : List FactorBlock).map factorBlockValue).prod) = 6910156909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_149
      · exact prime_twentySixX_1288247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6910156909) ^ 3455078454 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 2303385636 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 46376892 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 5364 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_9144957047 : Nat.Prime 9144957047 := by
  apply lucas_primality 9144957047 (5 : ZMod 9144957047)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1229, 1), (3720487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1229, 1), (3720487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9144957047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_1229
      · exact prime_twentySixX_3720487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9144957047) ^ 4572478523 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9144957047) ^ 7440974 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9144957047) ^ 2458 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_9456603047 : Nat.Prime 9456603047 := by
  apply lucas_primality 9456603047 (5 : ZMod 9456603047)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9456603047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentySixX_429845593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9456603047) ^ 4728301523 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 859691186 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 22 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_11928834361 : Nat.Prime 11928834361 := by
  apply lucas_primality 11928834361 (7 : ZMod 11928834361)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11928834361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_211
      · exact prime_twentySixX_17449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11928834361) ^ 5964417180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 3976278120 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 2385766872 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 56534760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 683640 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_11973719881 : Nat.Prime 11973719881 := by
  apply lucas_primality 11973719881 (11 : ZMod 11973719881)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (73, 1), (673, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (73, 1), (673, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 11973719881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_73
      · exact prime_t64_673
      · exact prime_twentySixX_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11973719881) ^ 5986859940 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11973719881) ^ 3991239960 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11973719881) ^ 2394743976 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11973719881) ^ 164023560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11973719881) ^ 17791560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11973719881) ^ 17686440 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_13001360959 : Nat.Prime 13001360959 := by
  apply lucas_primality 13001360959 (3 : ZMod 13001360959)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) = 13001360959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_t64_229
      · exact prime_twentySixX_85247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13001360959) ^ 6500680479 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 4333786986 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 351388134 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 56774502 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 152514 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_17499900673 : Nat.Prime 17499900673 := by
  apply lucas_primality 17499900673 (5 : ZMod 17499900673)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (7595443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (7595443, 1)] : List FactorBlock).map factorBlockValue).prod) = 17499900673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_7595443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 17499900673) ^ 8749950336 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17499900673) ^ 5833300224 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17499900673) ^ 2304 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18115486199 : Nat.Prime 18115486199 := by
  apply lucas_primality 18115486199 (13 : ZMod 18115486199)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5701, 1), (83621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5701, 1), (83621, 1)] : List FactorBlock).map factorBlockValue).prod) = 18115486199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentySixX_5701
      · exact prime_twentySixX_83621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 18115486199) ^ 9057743099 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 953446642 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 3177598 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 216638 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_19167809209 : Nat.Prime 19167809209 := by
  apply lucas_primality 19167809209 (7 : ZMod 19167809209)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) = 19167809209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_3011
      · exact prime_twentySixX_265247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19167809209) ^ 9583904604 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6389269736 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6365928 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 72264 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_19900204619 : Nat.Prime 19900204619 := by
  apply lucas_primality 19900204619 (2 : ZMod 19900204619)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) = 19900204619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_4243
      · exact prime_twentySixX_335009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19900204619) ^ 9950102309 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 2842886374 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 4690126 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 59402 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_23111364013 : Nat.Prime 23111364013 := by
  apply lucas_primality 23111364013 (2 : ZMod 23111364013)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (307, 1), (331, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (307, 1), (331, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) = 23111364013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_307
      · exact prime_twentySixX_331
      · exact prime_twentySixX_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23111364013) ^ 11555682006 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 7703788004 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 2101033092 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 75281316 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 69822852 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23111364013) ^ 13413444 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_23210693491 : Nat.Prime 23210693491 := by
  apply lucas_primality 23210693491 (10 : ZMod 23210693491)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3119, 1), (248057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3119, 1), (248057, 1)] : List FactorBlock).map factorBlockValue).prod) = 23210693491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_3119
      · exact prime_twentySixX_248057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 23210693491) ^ 11605346745 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 7736897830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 4642138698 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 7441710 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 23210693491) ^ 93570 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_24580164613 : Nat.Prime 24580164613 := by
  apply lucas_primality 24580164613 (2 : ZMod 24580164613)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (120491003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (120491003, 1)] : List FactorBlock).map factorBlockValue).prod) = 24580164613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentySixX_120491003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24580164613) ^ 12290082306 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 8193388204 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 1445892036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24580164613) ^ 204 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_29486133581 : Nat.Prime 29486133581 := by
  apply lucas_primality 29486133581 (2 : ZMod 29486133581)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) = 29486133581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_1474306679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29486133581) ^ 14743066790 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 5897226716 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 20 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_36699648137 : Nat.Prime 36699648137 := by
  apply lucas_primality 36699648137 (3 : ZMod 36699648137)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (97, 1), (313, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (97, 1), (313, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) = 36699648137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_t64_97
      · exact prime_twentySixX_313
      · exact prime_twentySixX_2477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36699648137) ^ 18349824068 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 601633576 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 378346888 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 117251272 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 36699648137) ^ 14816168 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_41162461121 : Nat.Prime 41162461121 := by
  apply lucas_primality 41162461121 (3 : ZMod 41162461121)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 1), (101, 1), (115781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 1), (101, 1), (115781, 1)] : List FactorBlock).map factorBlockValue).prod) = 41162461121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_101
      · exact prime_twentySixX_115781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41162461121) ^ 20581230560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 8232492224 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 3742041920 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 407549120 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 355520 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_45092098991 : Nat.Prime 45092098991 := by
  apply lucas_primality 45092098991 (7 : ZMod 45092098991)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4509209899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4509209899, 1)] : List FactorBlock).map factorBlockValue).prod) = 45092098991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_4509209899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 45092098991) ^ 22546049495 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 45092098991) ^ 9018419798 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 45092098991) ^ 10 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_45387854167 : Nat.Prime 45387854167 := by
  apply lucas_primality 45387854167 (3 : ZMod 45387854167)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3167, 1), (2388583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3167, 1), (2388583, 1)] : List FactorBlock).map factorBlockValue).prod) = 45387854167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_3167
      · exact prime_twentySixX_2388583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45387854167) ^ 22693927083 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 45387854167) ^ 15129284722 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 45387854167) ^ 14331498 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 45387854167) ^ 19002 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_72863556869 : Nat.Prime 72863556869 := by
  apply lucas_primality 72863556869 (2 : ZMod 72863556869)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) = 72863556869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_t64_73
      · exact prime_twentySixX_5309207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72863556869) ^ 36431778434 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 1550288444 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 998130916 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 13724 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_77681756927 : Nat.Prime 77681756927 := by
  apply lucas_primality 77681756927 (5 : ZMod 77681756927)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6947, 1), (5591029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6947, 1), (5591029, 1)] : List FactorBlock).map factorBlockValue).prod) = 77681756927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_6947
      · exact prime_twentySixX_5591029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 77681756927) ^ 38840878463 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 77681756927) ^ 11182058 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 77681756927) ^ 13894 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_104941231333 : Nat.Prime 104941231333 := by
  apply lucas_primality 104941231333 (2 : ZMod 104941231333)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) = 104941231333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_t64_311
      · exact prime_twentySixX_85469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104941231333) ^ 52470615666 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 34980410444 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 14991604476 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 2232792156 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 337431612 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 1227828 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_104999404039 : Nat.Prime 104999404039 := by
  apply lucas_primality 104999404039 (3 : ZMod 104999404039)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17499900673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17499900673, 1)] : List FactorBlock).map factorBlockValue).prod) = 104999404039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_17499900673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104999404039) ^ 52499702019 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104999404039) ^ 34999801346 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 104999404039) ^ 6 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_105842008711 : Nat.Prime 105842008711 := by
  apply lucas_primality 105842008711 (3 : ZMod 105842008711)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (31784387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (31784387, 1)] : List FactorBlock).map factorBlockValue).prod) = 105842008711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_twentySixX_31784387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105842008711) ^ 52921004355 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 35280669570 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 21168401742 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 2860594830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 3330 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_118947318383 : Nat.Prime 118947318383 := by
  apply lucas_primality 118947318383 (10 : ZMod 118947318383)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (199, 1), (199109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (199, 1), (199109, 1)] : List FactorBlock).map factorBlockValue).prod) = 118947318383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_79
      · exact prime_twentySixX_199
      · exact prime_twentySixX_199109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 118947318383) ^ 59473659191 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 6260385178 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 1505662258 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 597725218 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 118947318383) ^ 597398 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_212140652989 : Nat.Prime 212140652989 := by
  apply lucas_primality 212140652989 (2 : ZMod 212140652989)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) = 212140652989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_twentySixX_39198199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212140652989) ^ 106070326494 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 70713550996 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 19285513908 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5174162268 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5412 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_213502379527 : Nat.Prime 213502379527 := by
  apply lucas_primality 213502379527 (3 : ZMod 213502379527)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) = 213502379527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_1317915923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213502379527) ^ 106751189763 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 71167459842 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 162 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_299647270477 : Nat.Prime 299647270477 := by
  apply lucas_primality 299647270477 (2 : ZMod 299647270477)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (15101, 1), (32423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (15101, 1), (32423, 1)] : List FactorBlock).map factorBlockValue).prod) = 299647270477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentySixX_15101
      · exact prime_twentySixX_32423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 299647270477) ^ 149823635238 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 99882423492 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 17626310028 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 19842876 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 299647270477) ^ 9241812 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_318960960511 : Nat.Prime 318960960511 := by
  apply lucas_primality 318960960511 (17 : ZMod 318960960511)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) = 318960960511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_9719
      · exact prime_twentySixX_1093943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 318960960511) ^ 159480480255 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 106320320170 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 63792192102 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 32818290 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 291570 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_329299688969 : Nat.Prime 329299688969 := by
  apply lucas_primality 329299688969 (3 : ZMod 329299688969)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41162461121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41162461121, 1)] : List FactorBlock).map factorBlockValue).prod) = 329299688969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_41162461121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 329299688969) ^ 164649844484 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 329299688969) ^ 8 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_351739863821 : Nat.Prime 351739863821 := by
  apply lucas_primality 351739863821 (2 : ZMod 351739863821)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (567322361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (567322361, 1)] : List FactorBlock).map factorBlockValue).prod) = 351739863821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_twentySixX_567322361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 351739863821) ^ 175869931910 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 351739863821) ^ 70347972764 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 351739863821) ^ 11346447220 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 351739863821) ^ 620 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_359479905341 : Nat.Prime 359479905341 := by
  apply lucas_primality 359479905341 (3 : ZMod 359479905341)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (89, 1), (311, 1), (503, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (89, 1), (311, 1), (503, 1), (1291, 1)] : List FactorBlock).map factorBlockValue).prod) = 359479905341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_89
      · exact prime_t64_311
      · exact prime_twentySixX_503
      · exact prime_twentySixX_1291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 359479905341) ^ 179739952670 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 71895981068 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 4039100060 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 1155883940 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 714671780 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 359479905341) ^ 278450740 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_375380267527 : Nat.Prime 375380267527 := by
  apply lucas_primality 375380267527 (5 : ZMod 375380267527)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) = 375380267527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentySixX_127
      · exact prime_t64_157
      · exact prime_twentySixX_95083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 375380267527) ^ 187690133763 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 125126755842 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 34125478866 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2955750138 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2390957118 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 3947922 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_446310088717 : Nat.Prime 446310088717 := by
  apply lucas_primality 446310088717 (5 : ZMod 446310088717)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (26669, 1), (44987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (26669, 1), (44987, 1)] : List FactorBlock).map factorBlockValue).prod) = 446310088717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_twentySixX_26669
      · exact prime_twentySixX_44987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 446310088717) ^ 223155044358 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446310088717) ^ 148770029572 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446310088717) ^ 14397099636 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446310088717) ^ 16735164 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 446310088717) ^ 9920868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_548528279441 : Nat.Prime 548528279441 := by
  apply lucas_primality 548528279441 (3 : ZMod 548528279441)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (6856603493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (6856603493, 1)] : List FactorBlock).map factorBlockValue).prod) = 548528279441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_6856603493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 548528279441) ^ 274264139720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 548528279441) ^ 109705655888 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 548528279441) ^ 80 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_580594587409 : Nat.Prime 580594587409 := by
  apply lucas_primality 580594587409 (19 : ZMod 580594587409)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (6563, 1), (55849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (6563, 1), (55849, 1)] : List FactorBlock).map factorBlockValue).prod) = 580594587409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentySixX_6563
      · exact prime_twentySixX_55849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 580594587409) ^ 290297293704 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 193531529136 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 52781326128 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 88464816 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 10395792 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_686228178967 : Nat.Prime 686228178967 := by
  apply lucas_primality 686228178967 (5 : ZMod 686228178967)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (358530919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (358530919, 1)] : List FactorBlock).map factorBlockValue).prod) = 686228178967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_29
      · exact prime_twentySixX_358530919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 686228178967) ^ 343114089483 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 686228178967) ^ 228742726322 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 686228178967) ^ 62384379906 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 686228178967) ^ 23663040654 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 686228178967) ^ 1914 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_738647515831 : Nat.Prime 738647515831 := by
  apply lucas_primality 738647515831 (3 : ZMod 738647515831)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (3919, 1), (897517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (3919, 1), (897517, 1)] : List FactorBlock).map factorBlockValue).prod) = 738647515831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentySixX_3919
      · exact prime_twentySixX_897517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 738647515831) ^ 369323757915 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 246215838610 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 147729503166 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 105521073690 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 188478570 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 738647515831) ^ 822990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_906007626637 : Nat.Prime 906007626637 := by
  apply lucas_primality 906007626637 (2 : ZMod 906007626637)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) = 906007626637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentySixX_220118471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906007626637) ^ 453003813318 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 302002542212 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 129429660948 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 4116 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_951075532889 : Nat.Prime 951075532889 := by
  apply lucas_primality 951075532889 (3 : ZMod 951075532889)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9144957047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9144957047, 1)] : List FactorBlock).map factorBlockValue).prod) = 951075532889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_9144957047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 951075532889) ^ 475537766444 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 951075532889) ^ 73159656376 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 951075532889) ^ 104 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1091817788989 : Nat.Prime 1091817788989 := by
  apply lucas_primality 1091817788989 (2 : ZMod 1091817788989)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20719, 1), (4391371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20719, 1), (4391371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091817788989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_20719
      · exact prime_twentySixX_4391371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1091817788989) ^ 545908894494 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 363939262996 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 52696452 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 248628 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1123160144339 : Nat.Prime 1123160144339 := by
  apply lucas_primality 1123160144339 (2 : ZMod 1123160144339)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (18115486199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (18115486199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123160144339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_twentySixX_18115486199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1123160144339) ^ 561580072169 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123160144339) ^ 36230972398 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123160144339) ^ 62 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1903276866263 : Nat.Prime 1903276866263 := by
  apply lucas_primality 1903276866263 (5 : ZMod 1903276866263)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (23210693491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (23210693491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1903276866263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_twentySixX_23210693491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1903276866263) ^ 951638433131 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903276866263) ^ 46421386982 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903276866263) ^ 82 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2097817565491 : Nat.Prime 2097817565491 := by
  apply lucas_primality 2097817565491 (17 : ZMod 2097817565491)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (103, 1), (991, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (103, 1), (991, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2097817565491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_103
      · exact prime_t64_991
      · exact prime_twentySixX_25373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2097817565491) ^ 1048908782745 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 699272521830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 419563513098 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 20367160830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 2116869390 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (17 : ZMod 2097817565491) ^ 82679130 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2903228044637 : Nat.Prime 2903228044637 := by
  apply lucas_primality 2903228044637 (2 : ZMod 2903228044637)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (79, 1), (8562377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (79, 1), (8562377, 1)] : List FactorBlock).map factorBlockValue).prod) = 2903228044637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_37
      · exact prime_t64_79
      · exact prime_twentySixX_8562377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2903228044637) ^ 1451614022318 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 100111311884 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 78465622828 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 36749722084 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 339068 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3272997965299 : Nat.Prime 3272997965299 := by
  apply lucas_primality 3272997965299 (2 : ZMod 3272997965299)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3272997965299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_719
      · exact prime_twentySixX_758692157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3272997965299) ^ 1636498982649 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 1090999321766 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4552152942 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4314 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3789773822459 : Nat.Prime 3789773822459 := by
  apply lucas_primality 3789773822459 (2 : ZMod 3789773822459)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (223, 1), (653634671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (223, 1), (653634671, 1)] : List FactorBlock).map factorBlockValue).prod) = 3789773822459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_223
      · exact prime_twentySixX_653634671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3789773822459) ^ 1894886911229 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3789773822459) ^ 291521063266 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3789773822459) ^ 16994501446 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3789773822459) ^ 5798 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5000095063219 : Nat.Prime 5000095063219 := by
  apply lucas_primality 5000095063219 (2 : ZMod 5000095063219)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (642871, 1), (1296293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (642871, 1), (1296293, 1)] : List FactorBlock).map factorBlockValue).prod) = 5000095063219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_642871
      · exact prime_twentySixX_1296293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5000095063219) ^ 2500047531609 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 1666698354406 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 7777758 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000095063219) ^ 3857226 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5452977238001 : Nat.Prime 5452977238001 := by
  apply lucas_primality 5452977238001 (3 : ZMod 5452977238001)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) = 5452977238001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_twentySixX_3877
      · exact prime_twentySixX_37013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5452977238001) ^ 2726488619000 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1090595447600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 286998802000 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1406494000 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 147326000 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_7070795998229 : Nat.Prime 7070795998229 := by
  apply lucas_primality 7070795998229 (2 : ZMod 7070795998229)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (4211, 1), (1125419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (4211, 1), (1125419, 1)] : List FactorBlock).map factorBlockValue).prod) = 7070795998229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_373
      · exact prime_twentySixX_4211
      · exact prime_twentySixX_1125419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7070795998229) ^ 3535397999114 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 18956557636 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 1679125148 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7070795998229) ^ 6282812 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_11888851128907 : Nat.Prime 11888851128907 := by
  apply lucas_primality 11888851128907 (3 : ZMod 11888851128907)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) = 11888851128907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_89
      · exact prime_twentySixX_3041
      · exact prime_twentySixX_318313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11888851128907) ^ 5944425564453 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3962950376302 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 516906570822 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 133582596954 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3909520266 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 37349562 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_12291142418257 : Nat.Prime 12291142418257 := by
  apply lucas_primality 12291142418257 (5 : ZMod 12291142418257)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (83, 1), (237317393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (83, 1), (237317393, 1)] : List FactorBlock).map factorBlockValue).prod) = 12291142418257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_83
      · exact prime_twentySixX_237317393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12291142418257) ^ 6145571209128 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 4097047472752 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 945472493712 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 148086053232 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 12291142418257) ^ 51792 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18349824068501 : Nat.Prime 18349824068501 := by
  apply lucas_primality 18349824068501 (2 : ZMod 18349824068501)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (36699648137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (36699648137, 1)] : List FactorBlock).map factorBlockValue).prod) = 18349824068501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_36699648137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18349824068501) ^ 9174912034250 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18349824068501) ^ 3669964813700 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18349824068501) ^ 500 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_24705200084659 : Nat.Prime 24705200084659 := by
  apply lucas_primality 24705200084659 (2 : ZMod 24705200084659)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) = 24705200084659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_229
      · exact prime_twentySixX_12569
      · exact prime_twentySixX_1430543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24705200084659) ^ 12352600042329 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 8235066694886 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 107882969802 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 1965566082 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 17269806 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_26766338248187 : Nat.Prime 26766338248187 := by
  apply lucas_primality 26766338248187 (2 : ZMod 26766338248187)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (576523, 1), (23213591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (576523, 1), (23213591, 1)] : List FactorBlock).map factorBlockValue).prod) = 26766338248187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_576523
      · exact prime_twentySixX_23213591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26766338248187) ^ 13383169124093 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26766338248187) ^ 46427182 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 26766338248187) ^ 1153046 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_28322570842457 : Nat.Prime 28322570842457 := by
  apply lucas_primality 28322570842457 (5 : ZMod 28322570842457)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28322570842457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_twentySixX_5569
      · exact prime_twentySixX_3399569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28322570842457) ^ 14161285421228 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 2574779167496 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 1666033578968 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 5085755224 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 8331224 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_48717929959499 : Nat.Prime 48717929959499 := by
  apply lucas_primality 48717929959499 (2 : ZMod 48717929959499)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (491, 1), (297071417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (491, 1), (297071417, 1)] : List FactorBlock).map factorBlockValue).prod) = 48717929959499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_167
      · exact prime_t64_491
      · exact prime_twentySixX_297071417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48717929959499) ^ 24358964979749 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48717929959499) ^ 291724131494 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48717929959499) ^ 99221853278 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 48717929959499) ^ 163994 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_50456514775123 : Nat.Prime 50456514775123 := by
  apply lucas_primality 50456514775123 (2 : ZMod 50456514775123)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) = 50456514775123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_2593
      · exact prime_twentySixX_360347051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50456514775123) ^ 25228257387561 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 16818838258374 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 19458740754 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 140022 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_63384300983279 : Nat.Prime 63384300983279 := by
  apply lucas_primality 63384300983279 (11 : ZMod 63384300983279)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (23, 1), (67, 1), (109978417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (23, 1), (67, 1), (109978417, 1)] : List FactorBlock).map factorBlockValue).prod) = 63384300983279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_67
      · exact prime_twentySixX_109978417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 63384300983279) ^ 31692150491639 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 63384300983279) ^ 5762209180298 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 63384300983279) ^ 3728488293134 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 63384300983279) ^ 2755839173186 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 63384300983279) ^ 946034343034 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 63384300983279) ^ 576334 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_92532287279743 : Nat.Prime 92532287279743 := by
  apply lucas_primality 92532287279743 (5 : ZMod 92532287279743)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (391873, 1), (39354709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (391873, 1), (39354709, 1)] : List FactorBlock).map factorBlockValue).prod) = 92532287279743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_391873
      · exact prime_twentySixX_39354709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 92532287279743) ^ 46266143639871 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92532287279743) ^ 30844095759914 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92532287279743) ^ 236128254 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 92532287279743) ^ 2351238 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_102102247358591 : Nat.Prime 102102247358591 := by
  apply lucas_primality 102102247358591 (14 : ZMod 102102247358591)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) = 102102247358591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_523
      · exact prime_twentySixX_10159
      · exact prime_twentySixX_1921687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 102102247358591) ^ 51051123679295 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 20420449471718 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 195224182330 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 10050423010 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 53131570 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_119134327776067 : Nat.Prime 119134327776067 := by
  apply lucas_primality 119134327776067 (7 : ZMod 119134327776067)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119134327776067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_twentySixX_213502379527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119134327776067) ^ 59567163888033 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 39711442592022 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 3843042831486 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 558 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_142186425822187 : Nat.Prime 142186425822187 := by
  apply lucas_primality 142186425822187 (2 : ZMod 142186425822187)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (524453, 1), (852559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (524453, 1), (852559, 1)] : List FactorBlock).map factorBlockValue).prod) = 142186425822187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_twentySixX_524453
      · exact prime_twentySixX_852559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 142186425822187) ^ 71093212911093 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142186425822187) ^ 47395475274062 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142186425822187) ^ 2682762751362 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142186425822187) ^ 271113762 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142186425822187) ^ 166776054 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_160284903568781 : Nat.Prime 160284903568781 := by
  apply lucas_primality 160284903568781 (2 : ZMod 160284903568781)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) = 160284903568781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_61
      · exact prime_t64_113
      · exact prime_twentySixX_68392019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160284903568781) ^ 80142451784390 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 32056980713756 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 9428523739340 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2627621369980 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 1418450474060 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2343620 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_184625437429159 : Nat.Prime 184625437429159 := by
  apply lucas_primality 184625437429159 (19 : ZMod 184625437429159)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (277, 1), (1093, 1), (49409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (277, 1), (1093, 1), (49409, 1)] : List FactorBlock).map factorBlockValue).prod) = 184625437429159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_twentySixX_277
      · exact prime_t64_1093
      · exact prime_twentySixX_49409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 184625437429159) ^ 92312718714579 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 61541812476386 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 16784130675378 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 10860319848774 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 666517824654 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 168916228206 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 184625437429159) ^ 3736676262 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_226043412291283 : Nat.Prime 226043412291283 := by
  apply lucas_primality 226043412291283 (2 : ZMod 226043412291283)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) = 226043412291283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_359
      · exact prime_twentySixX_104941231333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226043412291283) ^ 113021706145641 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 75347804097094 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 629647387998 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 2154 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_304128603975499 : Nat.Prime 304128603975499 := by
  apply lucas_primality 304128603975499 (3 : ZMod 304128603975499)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) = 304128603975499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_103
      · exact prime_twentySixX_3109
      · exact prime_twentySixX_158288029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 304128603975499) ^ 152064301987749 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 101376201325166 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 2952704892966 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 97822001922 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 1921362 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_332196900026297 : Nat.Prime 332196900026297 := by
  apply lucas_primality 332196900026297 (3 : ZMod 332196900026297)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (821, 1), (954303599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (821, 1), (954303599, 1)] : List FactorBlock).map factorBlockValue).prod) = 332196900026297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentySixX_821
      · exact prime_twentySixX_954303599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332196900026297) ^ 166098450013148 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332196900026297) ^ 6267866038232 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332196900026297) ^ 404624725976 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 332196900026297) ^ 348104 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_366444555641737 : Nat.Prime 366444555641737 := by
  apply lucas_primality 366444555641737 (5 : ZMod 366444555641737)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) = 366444555641737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentySixX_487
      · exact prime_twentySixX_1381
      · exact prime_twentySixX_158759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 366444555641737) ^ 183222277820868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 122148185213912 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 33313141421976 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 28188042741672 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 752452886328 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 265347252456 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 2308181304 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_375886089384859 : Nat.Prime 375886089384859 := by
  apply lucas_primality 375886089384859 (7 : ZMod 375886089384859)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (278911, 1), (1919789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (278911, 1), (1919789, 1)] : List FactorBlock).map factorBlockValue).prod) = 375886089384859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentySixX_278911
      · exact prime_twentySixX_1919789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 375886089384859) ^ 187943044692429 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 125295363128286 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 28914314568066 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 1347691878 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 375886089384859) ^ 195795522 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_443609722217929 : Nat.Prime 443609722217929 := by
  apply lucas_primality 443609722217929 (13 : ZMod 443609722217929)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (29, 1), (31, 1), (421, 1), (6976699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (29, 1), (31, 1), (421, 1), (6976699, 1)] : List FactorBlock).map factorBlockValue).prod) = 443609722217929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_421
      · exact prime_twentySixX_6976699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 443609722217929) ^ 221804861108964 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 147869907405976 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 63372817459704 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 15296886973032 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 14309991039288 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 1053704803368 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (13 : ZMod 443609722217929) ^ 63584472 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_581810508705311 : Nat.Prime 581810508705311 := by
  apply lucas_primality 581810508705311 (7 : ZMod 581810508705311)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (995117, 1), (1243969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (995117, 1), (1243969, 1)] : List FactorBlock).map factorBlockValue).prod) = 581810508705311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_47
      · exact prime_twentySixX_995117
      · exact prime_twentySixX_1243969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 581810508705311) ^ 290905254352655 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 116362101741062 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 12378946993730 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 584665430 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 581810508705311) ^ 467704990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_585686675729543 : Nat.Prime 585686675729543 := by
  apply lucas_primality 585686675729543 (5 : ZMod 585686675729543)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2789, 1), (104999404039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2789, 1), (104999404039, 1)] : List FactorBlock).map factorBlockValue).prod) = 585686675729543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_2789
      · exact prime_twentySixX_104999404039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 585686675729543) ^ 292843337864771 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 585686675729543) ^ 209998808078 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 585686675729543) ^ 5578 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_909545717390161 : Nat.Prime 909545717390161 := by
  apply lucas_primality 909545717390161 (7 : ZMod 909545717390161)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (3789773822459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (3789773822459, 1)] : List FactorBlock).map factorBlockValue).prod) = 909545717390161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_3789773822459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 909545717390161) ^ 454772858695080 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 909545717390161) ^ 303181905796720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 909545717390161) ^ 181909143478032 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 909545717390161) ^ 240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1091318243936369 : Nat.Prime 1091318243936369 := by
  apply lucas_primality 1091318243936369 (3 : ZMod 1091318243936369)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091318243936369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_t64_59
      · exact prime_twentySixX_5327453741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1091318243936369) ^ 545659121968184 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 155902606276624 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 35203814320528 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 18496919388752 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 204848 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1159057776105457 : Nat.Prime 1159057776105457 := by
  apply lucas_primality 1159057776105457 (5 : ZMod 1159057776105457)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (71, 1), (257, 1), (1009, 1), (35447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (71, 1), (257, 1), (1009, 1), (35447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159057776105457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_t64_71
      · exact prime_twentySixX_257
      · exact prime_twentySixX_1009
      · exact prime_twentySixX_35447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1159057776105457) ^ 579528888052728 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 386352592035152 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 31325885840688 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 16324757409936 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 4509952436208 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 1148719302384 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 32698332048 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2274982813154993 : Nat.Prime 2274982813154993 := by
  apply lucas_primality 2274982813154993 (3 : ZMod 2274982813154993)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (142186425822187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (142186425822187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2274982813154993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_142186425822187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2274982813154993) ^ 1137491406577496 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2274982813154993) ^ 16 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3080389673224709 : Nat.Prime 3080389673224709 := by
  apply lucas_primality 3080389673224709 (2 : ZMod 3080389673224709)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3080389673224709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_967
      · exact prime_twentySixX_28229
      · exact prime_twentySixX_166931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3080389673224709) ^ 1540194836612354 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 236953051786516 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 3185511554524 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 109121459252 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 18453071468 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3300259784395591 : Nat.Prime 3300259784395591 := by
  apply lucas_primality 3300259784395591 (3 : ZMod 3300259784395591)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (75557, 1), (13116839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (75557, 1), (13116839, 1)] : List FactorBlock).map factorBlockValue).prod) = 3300259784395591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_twentySixX_75557
      · exact prime_twentySixX_13116839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3300259784395591) ^ 1650129892197795 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 1100086594798530 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 660051956879118 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 89196210389070 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 43679073870 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 251604810 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3674782224776989 : Nat.Prime 3674782224776989 := by
  apply lucas_primality 3674782224776989 (2 : ZMod 3674782224776989)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (173, 1), (45387854167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (173, 1), (45387854167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3674782224776989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentySixX_173
      · exact prime_twentySixX_45387854167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3674782224776989) ^ 1837391112388494 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3674782224776989) ^ 1224927408258996 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3674782224776989) ^ 282675555752076 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3674782224776989) ^ 21241515750156 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3674782224776989) ^ 80964 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5664798049611737 : Nat.Prime 5664798049611737 := by
  apply lucas_primality 5664798049611737 (3 : ZMod 5664798049611737)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (227873, 1), (63416971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (227873, 1), (63416971, 1)] : List FactorBlock).map factorBlockValue).prod) = 5664798049611737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_227873
      · exact prime_twentySixX_63416971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5664798049611737) ^ 2832399024805868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 809256864230248 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 24859452632 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 89326216 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6044419968107009 : Nat.Prime 6044419968107009 := by
  apply lucas_primality 6044419968107009 (3 : ZMod 6044419968107009)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (7561, 1), (1561368569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (7561, 1), (1561368569, 1)] : List FactorBlock).map factorBlockValue).prod) = 6044419968107009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_7561
      · exact prime_twentySixX_1561368569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6044419968107009) ^ 3022209984053504 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6044419968107009) ^ 799420707328 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6044419968107009) ^ 3871232 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_7120870075094261 : Nat.Prime 7120870075094261 := by
  apply lucas_primality 7120870075094261 (2 : ZMod 7120870075094261)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (10631, 1), (41189, 1), (813107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (10631, 1), (41189, 1), (813107, 1)] : List FactorBlock).map factorBlockValue).prod) = 7120870075094261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_10631
      · exact prime_twentySixX_41189
      · exact prime_twentySixX_813107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7120870075094261) ^ 3560435037547130 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7120870075094261) ^ 1424174015018852 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7120870075094261) ^ 669821284460 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7120870075094261) ^ 172882810340 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7120870075094261) ^ 8757605180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_11752363494974261 : Nat.Prime 11752363494974261 := by
  apply lucas_primality 11752363494974261 (3 : ZMod 11752363494974261)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (18292397, 1), (32123629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (18292397, 1), (32123629, 1)] : List FactorBlock).map factorBlockValue).prod) = 11752363494974261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_18292397
      · exact prime_twentySixX_32123629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11752363494974261) ^ 5876181747487130 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11752363494974261) ^ 2350472698994852 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11752363494974261) ^ 642472580 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 11752363494974261) ^ 365847940 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_11895479753831941 : Nat.Prime 11895479753831941 := by
  apply lucas_primality 11895479753831941 (2 : ZMod 11895479753831941)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11895479753831941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentySixX_28322570842457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11895479753831941) ^ 5947739876915970 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 3965159917943980 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 2379095950766388 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 1699354250547420 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 420 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18843021286721663 : Nat.Prime 18843021286721663 := by
  apply lucas_primality 18843021286721663 (5 : ZMod 18843021286721663)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26669, 1), (274831, 1), (1285429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26669, 1), (274831, 1), (1285429, 1)] : List FactorBlock).map factorBlockValue).prod) = 18843021286721663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_26669
      · exact prime_twentySixX_274831
      · exact prime_twentySixX_1285429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18843021286721663) ^ 9421510643360831 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 706551474998 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 68562212002 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 18843021286721663) ^ 14658935878 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_25024350819790243 : Nat.Prime 25024350819790243 := by
  apply lucas_primality 25024350819790243 (2 : ZMod 25024350819790243)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) = 25024350819790243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_47149
      · exact prime_twentySixX_29486133581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25024350819790243) ^ 12512175409895121 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 8341450273263414 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 530750404458 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 848682 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_27793292736046007 : Nat.Prime 27793292736046007 := by
  apply lucas_primality 27793292736046007 (5 : ZMod 27793292736046007)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (61, 1), (257, 1), (7219, 1), (9445537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (61, 1), (257, 1), (7219, 1), (9445537, 1)] : List FactorBlock).map factorBlockValue).prod) = 27793292736046007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_61
      · exact prime_twentySixX_257
      · exact prime_twentySixX_7219
      · exact prime_twentySixX_9445537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27793292736046007) ^ 13896646368023003 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 2137945595080462 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 455627749771246 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 108145107922358 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 3850019772274 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 2942478838 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_30133561870930829 : Nat.Prime 30133561870930829 := by
  apply lucas_primality 30133561870930829 (2 : ZMod 30133561870930829)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) = 30133561870930829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_twentySixX_160284903568781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30133561870930829) ^ 15066780935465414 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 641139614275124 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 188 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_50467968185178619 : Nat.Prime 50467968185178619 := by
  apply lucas_primality 50467968185178619 (2 : ZMod 50467968185178619)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (149, 1), (271, 1), (1049, 1), (1051, 1), (62981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (149, 1), (271, 1), (1049, 1), (1051, 1), (62981, 1)] : List FactorBlock).map factorBlockValue).prod) = 50467968185178619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_149
      · exact prime_twentySixX_271
      · exact prime_twentySixX_1049
      · exact prime_t64_1051
      · exact prime_twentySixX_62981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50467968185178619) ^ 25233984092589309 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 16822656061726206 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 338711195873682 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 186228664889958 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 48110551177482 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 48018999224718 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 50467968185178619) ^ 801320528178 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_93140068283564521 : Nat.Prime 93140068283564521 := by
  apply lucas_primality 93140068283564521 (11 : ZMod 93140068283564521)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (2309477, 1), (336079223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (2309477, 1), (336079223, 1)] : List FactorBlock).map factorBlockValue).prod) = 93140068283564521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_2309477
      · exact prime_twentySixX_336079223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 93140068283564521) ^ 46570034141782260 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 93140068283564521) ^ 31046689427854840 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 93140068283564521) ^ 18628013656712904 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 93140068283564521) ^ 40329506760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 93140068283564521) ^ 277137240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_171663126899945669 : Nat.Prime 171663126899945669 := by
  apply lucas_primality 171663126899945669 (2 : ZMod 171663126899945669)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (479, 1), (299647270477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (479, 1), (299647270477, 1)] : List FactorBlock).map factorBlockValue).prod) = 171663126899945669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_t64_479
      · exact prime_twentySixX_299647270477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171663126899945669) ^ 85831563449972834 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 13204855915380436 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 7463614213041116 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 358378135490492 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 171663126899945669) ^ 572884 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_239766403692867703 : Nat.Prime 239766403692867703 := by
  apply lucas_primality 239766403692867703 (3 : ZMod 239766403692867703)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) = 239766403692867703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_twentySixX_1753
      · exact prime_twentySixX_16097
      · exact prime_twentySixX_2273119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239766403692867703) ^ 119883201846433851 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 79922134564289234 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 34252343384695386 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 2694004535874918 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 136774902277734 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 14895098694966 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 105479037258 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_289273085672546347 : Nat.Prime 289273085672546347 := by
  apply lucas_primality 289273085672546347 (2 : ZMod 289273085672546347)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (199, 1), (2144047, 1), (16142521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (199, 1), (2144047, 1), (16142521, 1)] : List FactorBlock).map factorBlockValue).prod) = 289273085672546347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentySixX_199
      · exact prime_twentySixX_2144047
      · exact prime_twentySixX_16142521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 289273085672546347) ^ 144636542836273173 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 289273085672546347) ^ 96424361890848782 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 289273085672546347) ^ 41324726524649478 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 289273085672546347) ^ 1453633596344454 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 289273085672546347) ^ 134919190518 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 289273085672546347) ^ 17919944826 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_305561450869330787 : Nat.Prime 305561450869330787 := by
  apply lucas_primality 305561450869330787 (2 : ZMod 305561450869330787)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (11752363494974261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (11752363494974261, 1)] : List FactorBlock).map factorBlockValue).prod) = 305561450869330787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_11752363494974261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 305561450869330787) ^ 152780725434665393 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 305561450869330787) ^ 23504726989948522 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 305561450869330787) ^ 26 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_331297478798382559 : Nat.Prime 331297478798382559 := by
  apply lucas_primality 331297478798382559 (11 : ZMod 331297478798382559)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (19963, 1), (11973719881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (19963, 1), (11973719881, 1)] : List FactorBlock).map factorBlockValue).prod) = 331297478798382559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentySixX_19963
      · exact prime_twentySixX_11973719881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 331297478798382559) ^ 165648739399191279 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 331297478798382559) ^ 110432492932794186 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 331297478798382559) ^ 47328211256911794 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 331297478798382559) ^ 30117952618034778 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 331297478798382559) ^ 16595575755066 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (11 : ZMod 331297478798382559) ^ 27668718 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_426950491054489151 : Nat.Prime 426950491054489151 := by
  apply lucas_primality 426950491054489151 (7 : ZMod 426950491054489151)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) = 426950491054489151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_twentySixX_2767
      · exact prime_twentySixX_19167809209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 426950491054489151) ^ 213475245527244575 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 85390098210897830 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 60992927293498450 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 18563064828456050 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 154300864132450 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 22274350 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1421559306659942309 : Nat.Prime 1421559306659942309 := by
  apply lucas_primality 1421559306659942309 (2 : ZMod 1421559306659942309)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (2521, 1), (548528279441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (2521, 1), (548528279441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1421559306659942309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_257
      · exact prime_twentySixX_2521
      · exact prime_twentySixX_548528279441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1421559306659942309) ^ 710779653329971154 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 5531359169883044 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 563887071265348 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 2591588 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1471794749121262921 : Nat.Prime 1471794749121262921 := by
  apply lucas_primality 1471794749121262921 (7 : ZMod 1471794749121262921)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (61, 1), (293, 1), (686228178967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (61, 1), (293, 1), (686228178967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1471794749121262921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_twentySixX_293
      · exact prime_twentySixX_686228178967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1471794749121262921) ^ 735897374560631460 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1471794749121262921) ^ 490598249707087640 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1471794749121262921) ^ 294358949824252584 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1471794749121262921) ^ 24127782772479720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1471794749121262921) ^ 5023190270038440 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1471794749121262921) ^ 2144760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1561827409733979467 : Nat.Prime 1561827409733979467 := by
  apply lucas_primality 1561827409733979467 (2 : ZMod 1561827409733979467)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561827409733979467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_2767
      · exact prime_twentySixX_955337
      · exact prime_twentySixX_22724479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1561827409733979467) ^ 780913704866989733 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 120140569979536882 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 564447925454998 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 1634844468218 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 68728854454 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1603952514074243401 : Nat.Prime 1603952514074243401 := by
  apply lucas_primality 1603952514074243401 (7 : ZMod 1603952514074243401)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603952514074243401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_47
      · exact prime_twentySixX_67819
      · exact prime_twentySixX_2596501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603952514074243401) ^ 801976257037121700 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 534650838024747800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 320790502814848680 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 94350147886720200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 84418553372328600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 34126649235622200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 23650489008600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 617736143400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1976667271145826269 : Nat.Prime 1976667271145826269 := by
  apply lucas_primality 1976667271145826269 (2 : ZMod 1976667271145826269)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (5340763, 1), (864741887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (5340763, 1), (864741887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976667271145826269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_107
      · exact prime_twentySixX_5340763
      · exact prime_twentySixX_864741887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1976667271145826269) ^ 988333635572913134 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976667271145826269) ^ 18473525898559124 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976667271145826269) ^ 370109527636 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976667271145826269) ^ 2285846564 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2009831726809906421 : Nat.Prime 2009831726809906421 := by
  apply lucas_primality 2009831726809906421 (2 : ZMod 2009831726809906421)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009831726809906421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_557
      · exact prime_twentySixX_409901
      · exact prime_twentySixX_440144753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2009831726809906421) ^ 1004915863404953210 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 401966345361981284 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 3608315487989060 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4903212548420 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4566297140 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3077167559992740997 : Nat.Prime 3077167559992740997 := by
  apply lucas_primality 3077167559992740997 (2 : ZMod 3077167559992740997)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) = 3077167559992740997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_21569
      · exact prime_twentySixX_11888851128907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3077167559992740997) ^ 1538583779996370498 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 1025722519997580332 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 142666213546884 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 258828 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4018378747686678983 : Nat.Prime 4018378747686678983 := by
  apply lucas_primality 4018378747686678983 (5 : ZMod 4018378747686678983)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018378747686678983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_157
      · exact prime_t64_193
      · exact prime_twentySixX_14419
      · exact prime_twentySixX_4598633189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4018378747686678983) ^ 2009189373843339491 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 25594769093545726 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 20820615272987974 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 278686368519778 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 873820238 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_5891596123262137451 : Nat.Prime 5891596123262137451 := by
  apply lucas_primality 5891596123262137451 (2 : ZMod 5891596123262137451)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2613139, 1), (45092098991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2613139, 1), (45092098991, 1)] : List FactorBlock).map factorBlockValue).prod) = 5891596123262137451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_2613139
      · exact prime_twentySixX_45092098991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5891596123262137451) ^ 2945798061631068725 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5891596123262137451) ^ 1178319224652427490 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5891596123262137451) ^ 2254604949550 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5891596123262137451) ^ 130656950 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6026129309866944227 : Nat.Prime 6026129309866944227 := by
  apply lucas_primality 6026129309866944227 (2 : ZMod 6026129309866944227)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (10861, 1), (1123160144339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (10861, 1), (1123160144339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6026129309866944227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_twentySixX_10861
      · exact prime_twentySixX_1123160144339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6026129309866944227) ^ 3013064654933472113 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 463548408451303402 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 317164700519312854 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 554841111303466 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 5365334 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6276586759550679409 : Nat.Prime 6276586759550679409 := by
  apply lucas_primality 6276586759550679409 (7 : ZMod 6276586759550679409)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) = 6276586759550679409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentySixX_254927
      · exact prime_twentySixX_11928834361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6276586759550679409) ^ 3138293379775339704 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 2092195586516893136 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 145967133943039056 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 24621114121104 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 526169328 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_7777367187437459221 : Nat.Prime 7777367187437459221 := by
  apply lucas_primality 7777367187437459221 (6 : ZMod 7777367187437459221)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7777367187437459221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentySixX_367
      · exact prime_twentySixX_50456514775123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7777367187437459221) ^ 3888683593718729610 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 2592455729145819740 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1555473437487491844 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1111052455348208460 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 21191736205551660 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 154140 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_13145780685211854149 : Nat.Prime 13145780685211854149 := by
  apply lucas_primality 13145780685211854149 (2 : ZMod 13145780685211854149)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) = 13145780685211854149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_t64_67
      · exact prime_twentySixX_226043412291283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13145780685211854149) ^ 6572890342605927074 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 1877968669315979164 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 424057441458446908 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 196205681868833644 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 58156 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_17389510759726903703 : Nat.Prime 17389510759726903703 := by
  apply lucas_primality 17389510759726903703 (5 : ZMod 17389510759726903703)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (256889, 1), (1091817788989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (256889, 1), (1091817788989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17389510759726903703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_twentySixX_256889
      · exact prime_twentySixX_1091817788989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17389510759726903703) ^ 8694755379863451851 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 560951959991190442 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 67692702917318 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 15927118 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_18882334233565692523 : Nat.Prime 18882334233565692523 := by
  apply lucas_primality 18882334233565692523 (2 : ZMod 18882334233565692523)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1500157, 1), (2097817565491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1500157, 1), (2097817565491, 1)] : List FactorBlock).map factorBlockValue).prod) = 18882334233565692523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_1500157
      · exact prime_twentySixX_2097817565491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18882334233565692523) ^ 9441167116782846261 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 6294111411188564174 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 12586905392946 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 18882334233565692523) ^ 9000942 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_46854822292019384011 : Nat.Prime 46854822292019384011 := by
  apply lucas_primality 46854822292019384011 (2 : ZMod 46854822292019384011)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) = 46854822292019384011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_1561827409733979467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46854822292019384011) ^ 23427411146009692005 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 15618274097339794670 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 9370964458403876802 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 30 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_54435041108956384361 : Nat.Prime 54435041108956384361 := by
  apply lucas_primality 54435041108956384361 (6 : ZMod 54435041108956384361)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (243182789, 1), (508736671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (243182789, 1), (508736671, 1)] : List FactorBlock).map factorBlockValue).prod) = 54435041108956384361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentySixX_243182789
      · exact prime_twentySixX_508736671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54435041108956384361) ^ 27217520554478192180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 10887008221791276872 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 4948640100814216760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 223844135240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 54435041108956384361) ^ 107000427160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_67337590816601618489 : Nat.Prime 67337590816601618489 := by
  apply lucas_primality 67337590816601618489 (6 : ZMod 67337590816601618489)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67337590816601618489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_71
      · exact prime_twentySixX_9269333
      · exact prime_twentySixX_752335981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67337590816601618489) ^ 33668795408300809244 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 3961034753917742264 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 948416772064811528 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 7264556232536 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 89504679448 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_75529336934262770093 : Nat.Prime 75529336934262770093 := by
  apply lucas_primality 75529336934262770093 (2 : ZMod 75529336934262770093)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18882334233565692523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18882334233565692523, 1)] : List FactorBlock).map factorBlockValue).prod) = 75529336934262770093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_18882334233565692523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 75529336934262770093) ^ 37764668467131385046 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75529336934262770093) ^ 4 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_75535825166031223453 : Nat.Prime 75535825166031223453 := by
  apply lucas_primality 75535825166031223453 (2 : ZMod 75535825166031223453)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (331297478798382559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (331297478798382559, 1)] : List FactorBlock).map factorBlockValue).prod) = 75535825166031223453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentySixX_331297478798382559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75535825166031223453) ^ 37767912583015611726 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75535825166031223453) ^ 25178608388677074484 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75535825166031223453) ^ 3975569745580590708 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 75535825166031223453) ^ 228 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_82651541869666928401 : Nat.Prime 82651541869666928401 := by
  apply lucas_primality 82651541869666928401 (14 : ZMod 82651541869666928401)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (11, 1), (23, 2), (6379, 1), (1855533307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (11, 1), (23, 2), (6379, 1), (1855533307, 1)] : List FactorBlock).map factorBlockValue).prod) = 82651541869666928401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentySixX_6379
      · exact prime_twentySixX_1855533307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 82651541869666928401) ^ 41325770934833464200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 27550513956555642800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 16530308373933385680 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 7513776533606084400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 3593545298681170800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 12956817976119600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (14 : ZMod 82651541869666928401) ^ 44543281200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_107511351632581351121 : Nat.Prime 107511351632581351121 := by
  apply lucas_primality 107511351632581351121 (3 : ZMod 107511351632581351121)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (3011117, 1), (446310088717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (3011117, 1), (446310088717, 1)] : List FactorBlock).map factorBlockValue).prod) = 107511351632581351121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_3011117
      · exact prime_twentySixX_446310088717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 107511351632581351121) ^ 53755675816290675560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 107511351632581351121) ^ 21502270326516270224 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 107511351632581351121) ^ 35704807097360 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 107511351632581351121) ^ 240889360 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_130004395631094960253 : Nat.Prime 130004395631094960253 := by
  apply lucas_primality 130004395631094960253 (2 : ZMod 130004395631094960253)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) = 130004395631094960253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_146173
      · exact prime_twentySixX_24705200084659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130004395631094960253) ^ 65002197815547480126 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 43334798543698320084 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 889387203047724 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 5262228 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_188531075944388398433 : Nat.Prime 188531075944388398433 := by
  apply lucas_primality 188531075944388398433 (3 : ZMod 188531075944388398433)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5891596123262137451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5891596123262137451, 1)] : List FactorBlock).map factorBlockValue).prod) = 188531075944388398433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_5891596123262137451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 188531075944388398433) ^ 94265537972194199216 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 188531075944388398433) ^ 32 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_286099355001209160109 : Nat.Prime 286099355001209160109 := by
  apply lucas_primality 286099355001209160109 (6 : ZMod 286099355001209160109)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (200438423, 1), (118947318383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (200438423, 1), (118947318383, 1)] : List FactorBlock).map factorBlockValue).prod) = 286099355001209160109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_200438423
      · exact prime_twentySixX_118947318383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 286099355001209160109) ^ 143049677500604580054 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 95366451667069720036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 1427367820596 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (6 : ZMod 286099355001209160109) ^ 2405261076 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_344137326892735588579 : Nat.Prime 344137326892735588579 := by
  apply lucas_primality 344137326892735588579 (2 : ZMod 344137326892735588579)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (714283, 1), (26766338248187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (714283, 1), (26766338248187, 1)] : List FactorBlock).map factorBlockValue).prod) = 344137326892735588579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_714283
      · exact prime_twentySixX_26766338248187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344137326892735588579) ^ 172068663446367794289 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 114712442297578529526 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 481794088467366 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 344137326892735588579) ^ 12857094 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_749677156672310144177 : Nat.Prime 749677156672310144177 := by
  apply lucas_primality 749677156672310144177 (3 : ZMod 749677156672310144177)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) = 749677156672310144177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_46854822292019384011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 749677156672310144177) ^ 374838578336155072088 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 749677156672310144177) ^ 16 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_924096500249201382167 : Nat.Prime 924096500249201382167 := by
  apply lucas_primality 924096500249201382167 (5 : ZMod 924096500249201382167)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) = 924096500249201382167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentySixX_1223
      · exact prime_twentySixX_168197789
      · exact prime_twentySixX_320879927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 924096500249201382167) ^ 462048250124600691083 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 132013785749885911738 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 755598119582339642 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 5494106110094 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 2879882543258 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1043046175479247871761 : Nat.Prime 1043046175479247871761 := by
  apply lucas_primality 1043046175479247871761 (19 : ZMod 1043046175479247871761)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (61, 1), (155693, 1), (421133, 1), (1086611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (61, 1), (155693, 1), (421133, 1), (1086611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1043046175479247871761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_twentySixX_155693
      · exact prime_twentySixX_421133
      · exact prime_twentySixX_1086611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1043046175479247871761) ^ 521523087739623935880 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 347682058493082623920 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 208609235095849574352 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 17099117630807342160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 6699377463850320 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 2476761914832720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (19 : ZMod 1043046175479247871761) ^ 959907616874160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2124561888099414885917 : Nat.Prime 2124561888099414885917 := by
  apply lucas_primality 2124561888099414885917 (2 : ZMod 2124561888099414885917)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2124561888099414885917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_131
      · exact prime_twentySixX_10801067
      · exact prime_twentySixX_375380267527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2124561888099414885917) ^ 1062280944049707442958 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 16218029680148205236 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 196699260184148 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 5659759108 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_3720151109024930829341 : Nat.Prime 3720151109024930829341 := by
  apply lucas_primality 3720151109024930829341 (10 : ZMod 3720151109024930829341)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720151109024930829341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_twentySixX_1873
      · exact prime_twentySixX_1091318243936369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3720151109024930829341) ^ 1860075554512465414670 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 744030221804986165868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 531450158432132975620 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 286165469924994679180 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 1986199203964191580 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 3408860 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4017232481722971149851 : Nat.Prime 4017232481722971149851 := by
  apply lucas_primality 4017232481722971149851 (2 : ZMod 4017232481722971149851)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1063, 1), (1373, 1), (18349824068501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1063, 1), (1373, 1), (18349824068501, 1)] : List FactorBlock).map factorBlockValue).prod) = 4017232481722971149851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_1063
      · exact prime_t64_1373
      · exact prime_twentySixX_18349824068501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4017232481722971149851) ^ 2008616240861485574925 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 1339077493907657049950 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 803446496344594229970 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 3779146266907780950 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 2925879447722484450 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4017232481722971149851) ^ 218924850 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_6436569643652877041843 : Nat.Prime 6436569643652877041843 := by
  apply lucas_primality 6436569643652877041843 (2 : ZMod 6436569643652877041843)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (18869, 1), (797947, 1), (1194121493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (18869, 1), (797947, 1), (1194121493, 1)] : List FactorBlock).map factorBlockValue).prod) = 6436569643652877041843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_179
      · exact prime_twentySixX_18869
      · exact prime_twentySixX_797947
      · exact prime_twentySixX_1194121493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6436569643652877041843) ^ 3218284821826438520921 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6436569643652877041843) ^ 35958489629345681798 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6436569643652877041843) ^ 341118747345003818 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6436569643652877041843) ^ 8066412485607286 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6436569643652877041843) ^ 5390213375594 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_14715695298318302263009 : Nat.Prime 14715695298318302263009 := by
  apply lucas_primality 14715695298318302263009 (7 : ZMod 14715695298318302263009)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (23, 1), (181, 1), (1153, 1), (2903228044637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (23, 1), (181, 1), (1153, 1), (2903228044637, 1)] : List FactorBlock).map factorBlockValue).prod) = 14715695298318302263009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentySixX_181
      · exact prime_t64_1153
      · exact prime_twentySixX_2903228044637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14715695298318302263009) ^ 7357847649159151131504 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 4905231766106100754336 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 1337790481665300205728 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 639812839057317489696 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 81302183968609404768 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 12762962097413965536 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 5068735584 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_16764676135348824717077 : Nat.Prime 16764676135348824717077 := by
  apply lucas_primality 16764676135348824717077 (2 : ZMod 16764676135348824717077)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) = 16764676135348824717077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_149
      · exact prime_twentySixX_4018378747686678983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16764676135348824717077) ^ 8382338067674412358538 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 2394953733621260673868 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 112514604935227011524 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 4172 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_24026509006479235936343 : Nat.Prime 24026509006479235936343 := by
  apply lucas_primality 24026509006479235936343 (5 : ZMod 24026509006479235936343)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) = 24026509006479235936343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentySixX_924096500249201382167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24026509006479235936343) ^ 12013254503239617968171 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 1848193000498402764334 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 26 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_25116282422222531860373 : Nat.Prime 25116282422222531860373 := by
  apply lucas_primality 25116282422222531860373 (2 : ZMod 25116282422222531860373)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (103, 1), (663203, 1), (7070795998229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (103, 1), (663203, 1), (7070795998229, 1)] : List FactorBlock).map factorBlockValue).prod) = 25116282422222531860373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_103
      · exact prime_twentySixX_663203
      · exact prime_twentySixX_7070795998229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25116282422222531860373) ^ 12558141211111265930186 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 1932021724786348604644 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 243847402157500309324 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 37871183366514524 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 25116282422222531860373) ^ 3552115268 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_35488876712505214361017 : Nat.Prime 35488876712505214361017 := by
  apply lucas_primality 35488876712505214361017 (5 : ZMod 35488876712505214361017)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23329171, 1), (63384300983279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23329171, 1), (63384300983279, 1)] : List FactorBlock).map factorBlockValue).prod) = 35488876712505214361017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentySixX_23329171
      · exact prime_twentySixX_63384300983279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35488876712505214361017) ^ 17744438356252607180508 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35488876712505214361017) ^ 11829625570835071453672 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35488876712505214361017) ^ 1521223223598696 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 35488876712505214361017) ^ 559900104 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_48053018012958471872687 : Nat.Prime 48053018012958471872687 := by
  apply lucas_primality 48053018012958471872687 (5 : ZMod 48053018012958471872687)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) = 48053018012958471872687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_24026509006479235936343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48053018012958471872687) ^ 24026509006479235936343 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 48053018012958471872687) ^ 2 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_57930558174113115402061 : Nat.Prime 57930558174113115402061 := by
  apply lucas_primality 57930558174113115402061 (2 : ZMod 57930558174113115402061)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1659491, 1), (581810508705311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1659491, 1), (581810508705311, 1)] : List FactorBlock).map factorBlockValue).prod) = 57930558174113115402061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentySixX_1659491
      · exact prime_twentySixX_581810508705311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57930558174113115402061) ^ 28965279087056557701030 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 19310186058037705134020 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 11586111634822623080412 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 34908630522318660 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 57930558174113115402061) ^ 99569460 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_67799354156158681010663 : Nat.Prime 67799354156158681010663 := by
  apply lucas_primality 67799354156158681010663 (5 : ZMod 67799354156158681010663)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (421, 1), (139939, 1), (738647515831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (421, 1), (139939, 1), (738647515831, 1)] : List FactorBlock).map factorBlockValue).prod) = 67799354156158681010663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_41
      · exact prime_t64_421
      · exact prime_twentySixX_139939
      · exact prime_twentySixX_738647515831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 67799354156158681010663) ^ 33899677078079340505331 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 3568387060850456895298 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 1653642784296553195382 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 161043596570448173422 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 484492201288837858 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 67799354156158681010663) ^ 91788509002 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_90753507406596180058621 : Nat.Prime 90753507406596180058621 := by
  apply lucas_primality 90753507406596180058621 (10 : ZMod 90753507406596180058621)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (251, 1), (6026129309866944227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (251, 1), (6026129309866944227, 1)] : List FactorBlock).map factorBlockValue).prod) = 90753507406596180058621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_251
      · exact prime_twentySixX_6026129309866944227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 90753507406596180058621) ^ 45376753703298090029310 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 30251169135532060019540 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 18150701481319236011724 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 361567758592016653620 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 15060 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_109858826130696412328971 : Nat.Prime 109858826130696412328971 := by
  apply lucas_primality 109858826130696412328971 (2 : ZMod 109858826130696412328971)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (1187, 1), (27793292736046007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (1187, 1), (27793292736046007, 1)] : List FactorBlock).map factorBlockValue).prod) = 109858826130696412328971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_twentySixX_1187
      · exact prime_twentySixX_27793292736046007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 109858826130696412328971) ^ 54929413065348206164485 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 36619608710232137442990 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 21971765226139282465794 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 2969157462991794927810 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 92551664811033203310 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 3952710 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_139027313372561641588853 : Nat.Prime 139027313372561641588853 := by
  apply lucas_primality 139027313372561641588853 (2 : ZMod 139027313372561641588853)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) = 139027313372561641588853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_107
      · exact prime_twentySixX_6203
      · exact prime_twentySixX_3080389673224709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139027313372561641588853) ^ 69513656686280820794426 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 8178077257209508328756 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 1299320685724875155036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 22412915262382982684 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 45133028 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_186885572632985037422759 : Nat.Prime 186885572632985037422759 := by
  apply lucas_primality 186885572632985037422759 (7 : ZMod 186885572632985037422759)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (521, 1), (456068273, 1), (1518372857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (521, 1), (456068273, 1), (1518372857, 1)] : List FactorBlock).map factorBlockValue).prod) = 186885572632985037422759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_t64_521
      · exact prime_twentySixX_456068273
      · exact prime_twentySixX_1518372857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 186885572632985037422759) ^ 93442786316492518711379 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 26697938947569291060394 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 5050961422513109119534 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 358705513690950167798 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 409775429901446 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (7 : ZMod 186885572632985037422759) ^ 123082793380694 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_192170014358067349070659 : Nat.Prime 192170014358067349070659 := by
  apply lucas_primality 192170014358067349070659 (2 : ZMod 192170014358067349070659)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (112741, 1), (6044419968107009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (112741, 1), (6044419968107009, 1)] : List FactorBlock).map factorBlockValue).prod) = 192170014358067349070659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_twentySixX_112741
      · exact prime_twentySixX_6044419968107009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192170014358067349070659) ^ 96085007179033674535329 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 192170014358067349070659) ^ 64056671452689116356886 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 192170014358067349070659) ^ 4088723709746113810014 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 192170014358067349070659) ^ 1704526431006176538 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 192170014358067349070659) ^ 31792962 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_720252565412469632018731 : Nat.Prime 720252565412469632018731 := by
  apply lucas_primality 720252565412469632018731 (2 : ZMod 720252565412469632018731)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) = 720252565412469632018731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_661
      · exact prime_twentySixX_2220277
      · exact prime_twentySixX_5452977238001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720252565412469632018731) ^ 360126282706234816009365 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 240084188470823210672910 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 144050513082493926403746 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 1089640794875143164930 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 324397615888679490 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 132084278730 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1121040809141990479770073 : Nat.Prime 1121040809141990479770073 := by
  apply lucas_primality 1121040809141990479770073 (5 : ZMod 1121040809141990479770073)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121040809141990479770073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentySixX_1733
      · exact prime_t64_1801
      · exact prime_twentySixX_39581
      · exact prime_twentySixX_19900204619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1121040809141990479770073) ^ 560520404570995239885036 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 373680269713996826590024 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 59002147849578446303688 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 646878712718978926584 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 622454641389222920472 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 28322700516459677112 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 56333129764488 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_2000581775898039632625799 : Nat.Prime 2000581775898039632625799 := by
  apply lucas_primality 2000581775898039632625799 (15 : ZMod 2000581775898039632625799)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (4017232481722971149851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (4017232481722971149851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2000581775898039632625799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_twentySixX_4017232481722971149851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 2000581775898039632625799) ^ 1000290887949019816312899 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 666860591966013210875266 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 24103394890337826899106 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (15 : ZMod 2000581775898039632625799) ^ 498 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_4610610317485132586664977 : Nat.Prime 4610610317485132586664977 := by
  apply lucas_primality 4610610317485132586664977 (3 : ZMod 4610610317485132586664977)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (101, 1), (1409, 1), (289273085672546347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (101, 1), (1409, 1), (289273085672546347, 1)] : List FactorBlock).map factorBlockValue).prod) = 4610610317485132586664977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_101
      · exact prime_t64_1409
      · exact prime_twentySixX_289273085672546347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4610610317485132586664977) ^ 2305305158742566293332488 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4610610317485132586664977) ^ 658658616783590369523568 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4610610317485132586664977) ^ 45649607103813193927376 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4610610317485132586664977) ^ 3272257145127844277264 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4610610317485132586664977) ^ 15938608 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_9175802682589068344864299 : Nat.Prime 9175802682589068344864299 := by
  apply lucas_primality 9175802682589068344864299 (3 : ZMod 9175802682589068344864299)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) = 9175802682589068344864299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentySixX_139027313372561641588853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9175802682589068344864299) ^ 4587901341294534172432149 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 3058600894196356114954766 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 834163880235369849533118 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 66 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_14856906228454992245188691 : Nat.Prime 14856906228454992245188691 := by
  apply lucas_primality 14856906228454992245188691 (2 : ZMod 14856906228454992245188691)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (359, 1), (2799187, 1), (31813867, 1), (46471379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (359, 1), (2799187, 1), (31813867, 1), (46471379, 1)] : List FactorBlock).map factorBlockValue).prod) = 14856906228454992245188691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentySixX_359
      · exact prime_twentySixX_2799187
      · exact prime_twentySixX_31813867
      · exact prime_twentySixX_46471379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14856906228454992245188691) ^ 7428453114227496122594345 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14856906228454992245188691) ^ 2971381245690998449037738 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14856906228454992245188691) ^ 41384139912130897618910 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14856906228454992245188691) ^ 5307579032217208870 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14856906228454992245188691) ^ 466994667088254070 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 14856906228454992245188691) ^ 319700136904803110 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_23921353297022084790113153 : Nat.Prime 23921353297022084790113153 := by
  apply lucas_primality 23921353297022084790113153 (3 : ZMod 23921353297022084790113153)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (186885572632985037422759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (186885572632985037422759, 1)] : List FactorBlock).map factorBlockValue).prod) = 23921353297022084790113153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentySixX_186885572632985037422759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 23921353297022084790113153) ^ 11960676648511042395056576 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (3 : ZMod 23921353297022084790113153) ^ 128 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_27372162944499892213085843 : Nat.Prime 27372162944499892213085843 := by
  apply lucas_primality 27372162944499892213085843 (2 : ZMod 27372162944499892213085843)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (47, 1), (463, 1), (8783, 1), (29270713, 1), (222398269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (47, 1), (463, 1), (8783, 1), (29270713, 1), (222398269, 1)] : List FactorBlock).map factorBlockValue).prod) = 27372162944499892213085843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_47
      · exact prime_twentySixX_463
      · exact prime_twentySixX_8783
      · exact prime_twentySixX_29270713
      · exact prime_twentySixX_222398269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27372162944499892213085843) ^ 13686081472249946106542921 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 2488378449499990201189622 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 582386445627657281129486 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 59119142428725469142734 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 3116493560799259047374 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 935138236793203234 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27372162944499892213085843) ^ 123077230176193018 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_384236737333417236941192521 : Nat.Prime 384236737333417236941192521 := by
  apply lucas_primality 384236737333417236941192521 (107 : ZMod 384236737333417236941192521)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 384236737333417236941192521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 384236737333417236941192521) ^ 192118368666708618470596260 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 128078912444472412313730840 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 76847347466683447388238504 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 54890962476202462420170360 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 34930612484856112449199320 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 29556672102570556687784040 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 22602161019612778643599560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 20222986175443012470589080 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 16705945101452923345269240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 13249542666669559894523880 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 12394733462368297965844920 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 10384776684686952349761960 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 9371627739839444803443720 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 8935738077521331091655640 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 8175249730498239083855160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 7249749761007872395116840 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 6512487073447749778664280 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 6298962907105200605593320 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_404459723508860249411781601 : Nat.Prime 404459723508860249411781601 := by
  apply lucas_primality 404459723508860249411781601 (89 : ZMod 404459723508860249411781601)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 404459723508860249411781601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 404459723508860249411781601) ^ 202229861754430124705890800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 134819907836286749803927200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 80891944701772049882356320 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 57779960501265749915968800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 36769065773532749946525600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 31112286423758480723983200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 23791748441697661730104800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 17585205369950445626599200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 13946887017546905152130400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 13047087855124524174573600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 10931343878617844578696800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 9864871305094152424677600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 9406040081601401149111200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 8605526032103409561952800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 7631315537903023573807200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 6855249550997631345962400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 6630487270637053269045600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_409852519822311719403938689 : Nat.Prime 409852519822311719403938689 := by
  apply lucas_primality 409852519822311719403938689 (67 : ZMod 409852519822311719403938689)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 409852519822311719403938689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 409852519822311719403938689) ^ 204926259911155859701969344 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 136617506607437239801312896 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 58550359974615959914848384 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 37259319983846519945812608 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 31527116909408593800302976 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 24108971754253630553172864 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 21571185253805879968628352 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 17819674774883118234953856 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 14132845511114197220825472 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 13221049026526184496901248 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 11077095130332749173079424 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 9996402922495407790339968 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 9531453949356086497766016 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 8720266379198121689445504 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 7733066411741730554791296 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 6946652878344266430575232 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 409852519822311719403938689) ^ 6718893767578880645966208 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_749730219187155584275497601 : Nat.Prime 749730219187155584275497601 := by
  apply lucas_primality 749730219187155584275497601 (73 : ZMod 749730219187155584275497601)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 749730219187155584275497601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 749730219187155584275497601) ^ 374865109593577792137748800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 249910073062385194758499200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 149946043837431116855099520 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 107104317026736512039356800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 68157292653377780388681600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 57671555322088891098115200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 44101777599244446133852800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 39459485220376609698710400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 32596966051615460185891200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 25852766178867433940534400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 24184845780230825299209600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 20262978896950150926364800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 17435586492724548471523200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 15951706791216076261180800 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 14145853192210482722179200 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 12707291850629755665686400 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (73 : ZMod 749730219187155584275497601) ^ 12290659330936976791401600 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem prime_twentySixX_1024631299555779298509846721 : Nat.Prime 1024631299555779298509846721 := by
  apply lucas_primality 1024631299555779298509846721 (67 : ZMod 1024631299555779298509846721)
  · rw [← twentySixXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024631299555779298509846721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1024631299555779298509846721) ^ 512315649777889649254923360 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 341543766518593099503282240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 204926259911155859701969344 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 146375899936539899787120960 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 93148299959616299864531520 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 78817792273521484500757440 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 60272429385634076382932160 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 53927963134514699921570880 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 44549186937207795587384640 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 35332113777785493052063680 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 33052622566315461242253120 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 27692737825831872932698560 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 24991007306238519475849920 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 23828634873390216244415040 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 21800665947995304223613760 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 19332666029354326386978240 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 17366632195860666076438080 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 16797234418947201614915520 ≠ 1
      rw [← twentySixXFastPow_eq_pow]
      decide

private theorem phi_twentySixX_30738938986673378955295401600 : Nat.totient 30738938986673378955295401600 = 4044855579943376624025600000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401601 : Nat.totient 30738938986673378955295401601 = 30220371431479004403054625920 := by
  rw [← show ((([(73, 1), (311, 1), (26828093, 1), (50467968185178619, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_73, prime_t64_311, prime_twentySixX_26828093, prime_twentySixX_50467968185178619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401602 : Nat.totient 30738938986673378955295401602 = 15353814775218152739085008000 := by
  rw [← show ((([(2, 1), (1021, 1), (25951, 1), (1582963, 1), (366444555641737, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentySixX_1021, prime_twentySixX_25951, prime_twentySixX_1582963, prime_twentySixX_366444555641737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401603 : Nat.totient 30738938986673378955295401603 = 20222648962865762102412176064 := by
  rw [← show ((([(3, 1), (79, 1), (1913, 1), (67799354156158681010663, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_79, prime_twentySixX_1913, prime_twentySixX_67799354156158681010663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401604 : Nat.totient 30738938986673378955295401604 = 15365941854818408187346172160 := by
  rw [← show ((([(2, 2), (4357, 1), (148272073, 1), (11895479753831941, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentySixX_4357, prime_twentySixX_148272073, prime_twentySixX_11895479753831941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401605 : Nat.totient 30738938986673378955295401605 = 24495465776150614825075867648 := by
  rw [← show ((([(5, 1), (257, 1), (23921353297022084790113153, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_twentySixX_257, prime_twentySixX_23921353297022084790113153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401606 : Nat.totient 30738938986673378955295401606 = 10245977729715976398070460064 := by
  rw [← show ((([(2, 1), (3, 1), (32029, 1), (667123, 1), (239766403692867703, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_32029, prime_twentySixX_667123, prime_twentySixX_239766403692867703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401607 : Nat.totient 30738938986673378955295401607 = 26320099676472319639279216320 := by
  rw [← show ((([(7, 1), (967, 1), (83423, 1), (54435041108956384361, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_twentySixX_967, prime_twentySixX_83423, prime_twentySixX_54435041108956384361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401608 : Nat.totient 30738938986673378955295401608 = 15282684364083763761154944000 := by
  rw [← show ((([(2, 3), (199, 1), (2311, 1), (5209, 1), (1603952514074243401, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentySixX_199, prime_twentySixX_2311, prime_twentySixX_5209, prime_twentySixX_1603952514074243401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401609 : Nat.totient 30738938986673378955295401609 = 20466115478778701630452769280 := by
  rw [← show ((([(3, 2), (773, 1), (359479905341, 1), (12291142418257, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentySixX_773, prime_twentySixX_359479905341, prime_twentySixX_12291142418257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401610 : Nat.totient 30738938986673378955295401610 = 12292468809755109184865829888 := by
  rw [← show ((([(2, 1), (5, 1), (4093, 1), (119653, 1), (6276586759550679409, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentySixX_4093, prime_twentySixX_119653, prime_twentySixX_6276586759550679409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401611 : Nat.totient 30738938986673378955295401611 = 27914054898917135071835712000 := by
  rw [← show ((([(11, 3), (1321, 1), (4091, 1), (11369, 1), (375886089384859, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_twentySixX_1321, prime_twentySixX_4091, prime_twentySixX_11369, prime_twentySixX_375886089384859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401612 : Nat.totient 30738938986673378955295401612 = 10236158730557213385528979200 := by
  rw [← show ((([(2, 2), (3, 1), (1093, 1), (21611, 1), (39791, 1), (209623, 1), (13001360959, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_1093, prime_twentySixX_21611, prime_twentySixX_39791, prime_twentySixX_209623, prime_twentySixX_13001360959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401613 : Nat.totient 30738938986673378955295401613 = 28374270226316623452091290624 := by
  rw [← show ((([(13, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401614 : Nat.totient 30738938986673378955295401614 = 13173830994107789172433960224 := by
  rw [← show ((([(2, 1), (7, 1), (72863556869, 1), (30133561870930829, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentySixX_72863556869, prime_twentySixX_30133561870930829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401615 : Nat.totient 30738938986673378955295401615 = 16393700429161472505772529664 := by
  rw [← show ((([(3, 1), (5, 1), (49277, 1), (242257, 1), (171663126899945669, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentySixX_49277, prime_twentySixX_242257, prime_twentySixX_171663126899945669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401616 : Nat.totient 30738938986673378955295401616 = 15369469489921085513213540000 := by
  rw [← show ((([(2, 4), (4499780951, 1), (426950491054489151, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentySixX_4499780951, prime_twentySixX_426950491054489151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401617 : Nat.totient 30738938986673378955295401617 = 28778249948022726534635016960 := by
  rw [← show ((([(17, 1), (191, 1), (27509, 1), (344137326892735588579, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_191, prime_twentySixX_27509, prime_twentySixX_344137326892735588579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401618 : Nat.totient 30738938986673378955295401618 = 10241991480165318167306340600 := by
  rw [← show ((([(2, 1), (3, 2), (2371, 1), (720252565412469632018731, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_2371, prime_twentySixX_720252565412469632018731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401619 : Nat.totient 30738938986673378955295401619 = 29100974921835489007682014080 := by
  rw [← show ((([(19, 1), (1447, 1), (1908980081, 1), (585686675729543, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_twentySixX_1447, prime_twentySixX_1908980081, prime_twentySixX_585686675729543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401620 : Nat.totient 30738938986673378955295401620 = 12295545833460479382668220800 := by
  rw [← show ((([(2, 2), (5, 1), (413141, 1), (3720151109024930829341, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentySixX_413141, prime_twentySixX_3720151109024930829341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401621 : Nat.totient 30738938986673378955295401621 = 17565107992158670786832772144 := by
  rw [← show ((([(3, 1), (7, 1), (77681756927, 1), (18843021286721663, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentySixX_77681756927, prime_twentySixX_18843021286721663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401622 : Nat.totient 30738938986673378955295401622 = 13972223748323563985524292320 := by
  rw [← show ((([(2, 1), (11, 1), (657653, 1), (2124561888099414885917, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentySixX_657653, prime_twentySixX_2124561888099414885917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401623 : Nat.totient 30738938986673378955295401623 = 29280266722511589567984537600 := by
  rw [← show ((([(23, 1), (241, 1), (150377, 1), (1595647661, 1), (23111364013, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_twentySixX_241, prime_twentySixX_150377, prime_twentySixX_1595647661, prime_twentySixX_23111364013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401624 : Nat.totient 30738938986673378955295401624 = 10246312933338855484281340800 := by
  rw [← show ((([(2, 3), (3, 1), (164681581, 1), (7777367187437459221, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_164681581, prime_twentySixX_7777367187437459221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401625 : Nat.totient 30738938986673378955295401625 = 24294252918783809640956094400 := by
  rw [← show ((([(5, 3), (83, 1), (39227, 1), (75529336934262770093, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_83, prime_twentySixX_39227, prime_twentySixX_75529336934262770093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401626 : Nat.totient 30738938986673378955295401626 = 14046657934239547674011714304 := by
  rw [← show ((([(2, 1), (13, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401627 : Nat.totient 30738938986673378955295401627 = 20427333104965878549299681280 := by
  rw [← show ((([(3, 5), (563, 1), (971, 1), (4397, 1), (8117, 1), (30853, 1), (210138469, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_563, prime_twentySixX_971, prime_twentySixX_4397, prime_twentySixX_8117, prime_twentySixX_30853, prime_twentySixX_210138469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401628 : Nat.totient 30738938986673378955295401628 = 13173830836539222757296502848 := by
  rw [← show ((([(2, 2), (7, 1), (83511149, 1), (13145780685211854149, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentySixX_83511149, prime_twentySixX_13145780685211854149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401629 : Nat.totient 30738938986673378955295401629 = 29655516575435572039625293824 := by
  rw [← show ((([(29, 1), (1279, 1), (128257, 1), (1292293, 1), (5000095063219, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_twentySixX_1279, prime_twentySixX_128257, prime_twentySixX_1292293, prime_twentySixX_5000095063219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401630 : Nat.totient 30738938986673378955295401630 = 8197050396446234388078773760 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1024631299555779298509846721, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentySixX_1024631299555779298509846721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401631 : Nat.totient 30738938986673378955295401631 = 29701488066383792443591584000 := by
  rw [← show ((([(31, 1), (653, 1), (94651, 1), (8429209, 1), (1903276866263, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_twentySixX_653, prime_twentySixX_94651, prime_twentySixX_8429209, prime_twentySixX_1903276866263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401632 : Nat.totient 30738938986673378955295401632 = 15366085210369260435385626624 := by
  rw [← show ((([(2, 5), (7057, 1), (15373, 1), (74323, 1), (119134327776067, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentySixX_7057, prime_twentySixX_15373, prime_twentySixX_74323, prime_twentySixX_119134327776067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401633 : Nat.totient 30738938986673378955295401633 = 18629639130999750387931008000 := by
  rw [← show ((([(3, 1), (11, 1), (893041, 1), (1043046175479247871761, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentySixX_893041, prime_twentySixX_1043046175479247871761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401634 : Nat.totient 30738938986673378955295401634 = 14462819214819577686848332800 := by
  rw [← show ((([(2, 1), (17, 1), (9437, 1), (20023, 1), (46861, 1), (102102247358591, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentySixX_9437, prime_twentySixX_20023, prime_twentySixX_46861, prime_twentySixX_102102247358591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401635 : Nat.totient 30738938986673378955295401635 = 21030115628240192618162388576 := by
  rw [← show ((([(5, 1), (7, 1), (439, 1), (2000581775898039632625799, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_t64_439, prime_twentySixX_2000581775898039632625799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401636 : Nat.totient 30738938986673378955295401636 = 10245501020440086076991494080 := by
  rw [← show ((([(2, 2), (3, 2), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_12619, prime_twentySixX_212140652989, prime_twentySixX_318960960511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401637 : Nat.totient 30738938986673378955295401637 = 29906071351804154695159454400 := by
  rw [← show ((([(37, 1), (14341, 1), (57930558174113115402061, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_twentySixX_14341, prime_twentySixX_57930558174113115402061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401638 : Nat.totient 30738938986673378955295401638 = 14556133525512236728237596000 := by
  rw [← show ((([(2, 1), (19, 1), (3391, 1), (118691, 1), (2009831726809906421, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentySixX_3391, prime_twentySixX_118691, prime_twentySixX_2009831726809906421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401639 : Nat.totient 30738938986673378955295401639 = 18858596751130786945731072000 := by
  rw [← show ((([(3, 1), (13, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401640 : Nat.totient 30738938986673378955295401640 = 12294933615168744834505728000 := by
  rw [← show ((([(2, 3), (5, 1), (19387, 1), (1584001, 1), (25024350819790243, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentySixX_19387, prime_twentySixX_1584001, prime_twentySixX_25024350819790243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401641 : Nat.totient 30738938986673378955295401641 = 29989208767486223371019904000 := by
  rw [← show ((([(41, 1), (749730219187155584275497601, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_twentySixX_749730219187155584275497601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401642 : Nat.totient 30738938986673378955295401642 = 8738280940274603382506607360 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (211, 1), (3299, 1), (1160494157, 1), (906007626637, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentySixX_211, prime_twentySixX_3299, prime_twentySixX_1160494157, prime_twentySixX_906007626637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401643 : Nat.totient 30738938986673378955295401643 = 29601155396838958526662992000 := by
  rw [← show ((([(43, 1), (71, 1), (590437, 1), (693751151, 1), (24580164613, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_71, prime_twentySixX_590437, prime_twentySixX_693751151, prime_twentySixX_24580164613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401644 : Nat.totient 30738938986673378955295401644 = 13813552207742565162094848000 := by
  rw [← show ((([(2, 2), (11, 1), (89, 1), (12301, 1), (24019, 1), (4553573, 1), (5834431507, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_89, prime_twentySixX_12301, prime_twentySixX_24019, prime_twentySixX_4553573, prime_twentySixX_5834431507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401645 : Nat.totient 30738938986673378955295401645 = 16393498002114335435392245888 := by
  rw [← show ((([(3, 2), (5, 1), (27197, 1), (25116282422222531860373, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentySixX_27197, prime_twentySixX_25116282422222531860373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401646 : Nat.totient 30738938986673378955295401646 = 14701228829181868659634723104 := by
  rw [← show ((([(2, 1), (23, 1), (5140117, 1), (130004395631094960253, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentySixX_5140117, prime_twentySixX_130004395631094960253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401647 : Nat.totient 30738938986673378955295401647 = 29883707048457299433432837600 := by
  rw [← show ((([(47, 1), (151, 1), (15139, 1), (286099355001209160109, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_twentySixX_151, prime_twentySixX_15139, prime_twentySixX_286099355001209160109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401648 : Nat.totient 30738938986673378955295401648 = 10238886467341811625646499328 := by
  rw [← show ((([(2, 4), (3, 1), (1907, 1), (4987, 1), (67337590816601618489, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_1907, prime_twentySixX_4987, prime_twentySixX_67337590816601618489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401649 : Nat.totient 30738938986673378955295401649 = 26347658517212423435352000000 := by
  rw [← show ((([(7, 2), (7590001, 1), (82651541869666928401, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_twentySixX_7590001, prime_twentySixX_82651541869666928401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401650 : Nat.totient 30738938986673378955295401650 = 12112059541017570215220873360 := by
  rw [← show ((([(2, 1), (5, 2), (67, 1), (9175802682589068344864299, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_67, prime_twentySixX_9175802682589068344864299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401651 : Nat.totient 30738938986673378955295401651 = 19088108476900541771248189440 := by
  rw [← show ((([(3, 1), (17, 1), (97, 1), (82261, 1), (75535825166031223453, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_97, prime_twentySixX_82261, prime_twentySixX_75535825166031223453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401652 : Nat.totient 30738938986673378955295401652 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 2), (13, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401653 : Nat.totient 30738938986673378955295401653 = 30158624304171279214075193104 := by
  rw [← show ((([(53, 1), (90107, 1), (6436569643652877041843, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_twentySixX_90107, prime_twentySixX_6436569643652877041843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401654 : Nat.totient 30738938986673378955295401654 = 10246299501368972883502204416 := by
  rw [← show ((([(2, 1), (3, 3), (759313, 1), (749677156672310144177, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_759313, prime_twentySixX_749677156672310144177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401655 : Nat.totient 30738938986673378955295401655 = 22185116588752842757185216000 := by
  rw [← show ((([(5, 1), (11, 1), (223, 1), (317, 1), (1110271, 1), (7120870075094261, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_t64_223, prime_t64_317, prime_twentySixX_1110271, prime_twentySixX_7120870075094261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401656 : Nat.totient 30738938986673378955295401656 = 13172677721856279977515667808 := by
  rw [← show ((([(2, 3), (7, 1), (11423, 1), (48053018012958471872687, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentySixX_11423, prime_twentySixX_48053018012958471872687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401657 : Nat.totient 30738938986673378955295401657 = 19413600892143011792081925120 := by
  rw [← show ((([(3, 1), (19, 1), (42181, 1), (3479089, 1), (3674782224776989, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_twentySixX_42181, prime_twentySixX_3479089, prime_twentySixX_3674782224776989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401658 : Nat.totient 30738938986673378955295401658 = 14645621071840733272837593600 := by
  rw [← show ((([(2, 1), (29, 1), (101, 1), (313, 1), (16764676135348824717077, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_t64_101, prime_twentySixX_313, prime_twentySixX_16764676135348824717077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401659 : Nat.totient 30738938986673378955295401659 = 29950524622383421282975684096 := by
  rw [← show ((([(59, 1), (113, 1), (4610610317485132586664977, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_t64_113, prime_twentySixX_4610610317485132586664977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401660 : Nat.totient 30738938986673378955295401660 = 8179113743499962540402445312 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (457, 1), (1121040809141990479770073, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentySixX_457, prime_twentySixX_1121040809141990479770073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401661 : Nat.totient 30738938986673378955295401661 = 30234859832244150638770063680 := by
  rw [← show ((([(61, 1), (187127, 1), (55275637, 1), (48717929959499, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_twentySixX_187127, prime_twentySixX_55275637, prime_twentySixX_48717929959499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401662 : Nat.totient 30738938986673378955295401662 = 14870538397534880565550836000 := by
  rw [← show ((([(2, 1), (31, 1), (5683, 1), (28351, 1), (3077167559992740997, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_twentySixX_5683, prime_twentySixX_28351, prime_twentySixX_3077167559992740997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401663 : Nat.totient 30738938986673378955295401663 = 17558189871867897549887880144 := by
  rw [← show ((([(3, 2), (7, 1), (2539, 1), (192170014358067349070659, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentySixX_2539, prime_twentySixX_192170014358067349070659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401664 : Nat.totient 30738938986673378955295401664 = 15277436740264002174838615296 := by
  rw [← show ((([(2, 6), (167, 1), (9456603047, 1), (304128603975499, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_167, prime_twentySixX_9456603047, prime_twentySixX_304128603975499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401665 : Nat.totient 30738938986673378955295401665 = 22599304408504195420770457344 := by
  rw [← show ((([(5, 1), (13, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401666 : Nat.totient 30738938986673378955295401666 = 9314826779049333877633858560 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (3089857, 1), (46053307, 1), (3272997965299, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_twentySixX_3089857, prime_twentySixX_46053307, prime_twentySixX_3272997965299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401667 : Nat.totient 30738938986673378955295401667 = 30738938879162027322428137120 := by
  rw [← show ((([(285913427, 1), (107511351632581351121, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_285913427, prime_twentySixX_107511351632581351121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401668 : Nat.totient 30738938986673378955295401668 = 14416013144522990009951669760 := by
  rw [← show ((([(2, 2), (17, 2), (293, 1), (90753507406596180058621, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentySixX_293, prime_twentySixX_90753507406596180058621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401669 : Nat.totient 30738938986673378955295401669 = 19600080741796079829016804608 := by
  rw [← show ((([(3, 1), (23, 1), (12553, 1), (35488876712505214361017, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_twentySixX_12553, prime_twentySixX_35488876712505214361017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401670 : Nat.totient 30738938986673378955295401670 = 10538538048040355431451154432 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (20029, 1), (18915877, 1), (1159057776105457, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_twentySixX_20029, prime_twentySixX_18915877, prime_twentySixX_1159057776105457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401671 : Nat.totient 30738938986673378955295401671 = 30738938986672954226108095632 := by
  rw [← show ((([(92532287279743, 1), (332196900026297, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_92532287279743, prime_twentySixX_332196900026297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401672 : Nat.totient 30738938986673378955295401672 = 10236960807486185345668365312 := by
  rw [← show ((([(2, 3), (3, 2), (1097, 1), (873139, 1), (64502783, 1), (6910156909, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_1097, prime_twentySixX_873139, prime_twentySixX_64502783, prime_twentySixX_6910156909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401673 : Nat.totient 30738938986673378955295401673 = 30582903763303756524182732160 := by
  rw [← show ((([(197, 1), (351739863821, 1), (443609722217929, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_197, prime_twentySixX_351739863821, prime_twentySixX_443609722217929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401674 : Nat.totient 30738938986673378955295401674 = 14748761570152835994750738432 := by
  rw [← show ((([(2, 1), (37, 2), (73, 1), (31817, 1), (5082277, 1), (951075532889, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_t64_73, prime_twentySixX_31817, prime_twentySixX_5082277, prime_twentySixX_951075532889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401675 : Nat.totient 30738938986673378955295401675 = 16394100792892468776157547520 := by
  rw [← show ((([(3, 1), (5, 2), (409852519822311719403938689, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentySixX_409852519822311719403938689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401676 : Nat.totient 30738938986673378955295401676 = 14560550046318968978824137600 := by
  rw [← show ((([(2, 2), (19, 1), (404459723508860249411781601, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentySixX_404459723508860249411781601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401677 : Nat.totient 30738938986673378955295401677 = 23951564150114472970118489280 := by
  rw [← show ((([(7, 1), (11, 1), (29879, 1), (480379, 1), (5534623, 1), (5025277307, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_twentySixX_29879, prime_twentySixX_480379, prime_twentySixX_5534623, prime_twentySixX_5025277307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401678 : Nat.totient 30738938986673378955295401678 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401679 : Nat.totient 30738938986673378955295401679 = 30724082080444923963050210920 := by
  rw [← show ((([(2069, 1), (14856906228454992245188691, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_2069, prime_twentySixX_14856906228454992245188691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401680 : Nat.totient 30738938986673378955295401680 = 12295575594669351582118160640 := by
  rw [← show ((([(2, 4), (5, 1), (384236737333417236941192521, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentySixX_384236737333417236941192521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401681 : Nat.totient 30738938986673378955295401681 = 20492625964623280472090639520 := by
  rw [← show ((([(3, 3), (773531243, 1), (1471794749121262921, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentySixX_773531243, prime_twentySixX_1471794749121262921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401682 : Nat.totient 30738938986673378955295401682 = 14684732344550373318667958400 := by
  rw [← show ((([(2, 1), (41, 1), (79, 1), (131, 1), (2083, 1), (17389510759726903703, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_t64_79, prime_twentySixX_131, prime_twentySixX_2083, prime_twentySixX_17389510759726903703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401683 : Nat.totient 30738938986673378955295401683 = 30738927473072576405432376768 := by
  rw [← show ((([(2795069, 1), (59566873, 1), (184625437429159, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_2795069, prime_twentySixX_59566873, prime_twentySixX_184625437429159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401684 : Nat.totient 30738938986673378955295401684 = 8779917384365257273331282400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (3331, 1), (109858826130696412328971, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentySixX_3331, prime_twentySixX_109858826130696412328971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401685 : Nat.totient 30738938986673378955295401685 = 23112945093065912265862668288 := by
  rw [← show ((([(5, 1), (17, 1), (733, 1), (249593, 1), (1976667271145826269, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_twentySixX_733, prime_twentySixX_249593, prime_twentySixX_1976667271145826269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401686 : Nat.totient 30738938986673378955295401686 = 14806226255793556458530025216 := by
  rw [← show ((([(2, 1), (43, 1), (107, 1), (227, 1), (14715695298318302263009, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_t64_107, prime_t64_227, prime_twentySixX_14715695298318302263009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401687 : Nat.totient 30738938986673378955295401687 = 19741317790031488414853456640 := by
  rw [← show ((([(3, 1), (29, 1), (443, 1), (8563067, 1), (93140068283564521, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_twentySixX_443, prime_twentySixX_8563067, prime_twentySixX_93140068283564521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401688 : Nat.totient 30738938986673378955295401688 = 13972244993810430354623556000 := by
  rw [← show ((([(2, 3), (11, 1), (105842008711, 1), (3300259784395591, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentySixX_105842008711, prime_twentySixX_3300259784395591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401689 : Nat.totient 30738938986673378955295401689 = 30711566823728879063082314724 := by
  rw [← show ((([(1123, 1), (27372162944499892213085843, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_1123, prime_twentySixX_27372162944499892213085843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401690 : Nat.totient 30738938986673378955295401690 = 8197050362328811022473919616 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (240259949, 1), (1421559306659942309, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentySixX_240259949, prime_twentySixX_1421559306659942309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401691 : Nat.totient 30738938986673378955295401691 = 24320669372195661355780101024 := by
  rw [← show ((([(7, 1), (13, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401692 : Nat.totient 30738938986673378955295401692 = 14695970098163565478332961280 := by
  rw [← show ((([(2, 2), (23, 1), (3203, 1), (21911, 1), (14457413, 1), (329299688969, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentySixX_3203, prime_twentySixX_21911, prime_twentySixX_14457413, prime_twentySixX_329299688969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401693 : Nat.totient 30738938986673378955295401693 = 19797192834802537623066823680 := by
  rw [← show ((([(3, 1), (31, 1), (577, 1), (1874699, 1), (305561450869330787, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_twentySixX_577, prime_twentySixX_1874699, prime_twentySixX_305561450869330787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401694 : Nat.totient 30738938986673378955295401694 = 15011571370279220445198224448 := by
  rw [← show ((([(2, 1), (47, 1), (487, 1), (118535279, 1), (5664798049611737, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_twentySixX_487, prime_twentySixX_118535279, prime_twentySixX_5664798049611737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401695 : Nat.totient 30738938986673378955295401695 = 23241755095752818753400720384 := by
  rw [← show ((([(5, 1), (19, 1), (479, 1), (3583, 1), (188531075944388398433, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_t64_479, prime_twentySixX_3583, prime_twentySixX_188531075944388398433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401696 : Nat.totient 30738938986673378955295401696 = 10239102194041466534621454336 := by
  rw [← show ((([(2, 5), (3, 1), (2383, 1), (3719, 1), (65713, 1), (9441539, 1), (58233559, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentySixX_2383, prime_twentySixX_3719, prime_twentySixX_65713, prime_twentySixX_9441539, prime_twentySixX_58233559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401697 : Nat.totient 30738938986673378955295401697 = 30738899673650756573984228160 := by
  rw [← show ((([(796583, 1), (42426119, 1), (909545717390161, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentySixX_796583, prime_twentySixX_42426119, prime_twentySixX_909545717390161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401698 : Nat.totient 30738938986673378955295401698 = 13085334521995466383390273536 := by
  rw [← show ((([(2, 1), (7, 2), (149, 1), (161717, 1), (22420633, 1), (580594587409, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_149, prime_twentySixX_161717, prime_twentySixX_22420633, prime_twentySixX_580594587409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentySixX_30738938986673378955295401699 : Nat.totient 30738938986673378955295401699 = 18625026351928577740483046400 := by
  rw [← show ((([(3, 2), (11, 1), (4021, 1), (33942317, 1), (2274982813154993, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738938986673378955295401699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentySixX_4021, prime_twentySixX_33942317, prime_twentySixX_2274982813154993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentySixX : certifiedKill 1 30738938986673378955295401599 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentySixX_30738938986673378955295401600, phi_twentySixX_30738938986673378955295401601, phi_twentySixX_30738938986673378955295401602,
    phi_twentySixX_30738938986673378955295401603, phi_twentySixX_30738938986673378955295401604, phi_twentySixX_30738938986673378955295401605,
    phi_twentySixX_30738938986673378955295401606, phi_twentySixX_30738938986673378955295401607, phi_twentySixX_30738938986673378955295401608,
    phi_twentySixX_30738938986673378955295401609, phi_twentySixX_30738938986673378955295401610, phi_twentySixX_30738938986673378955295401611,
    phi_twentySixX_30738938986673378955295401612, phi_twentySixX_30738938986673378955295401613, phi_twentySixX_30738938986673378955295401614,
    phi_twentySixX_30738938986673378955295401615, phi_twentySixX_30738938986673378955295401616, phi_twentySixX_30738938986673378955295401617,
    phi_twentySixX_30738938986673378955295401618, phi_twentySixX_30738938986673378955295401619, phi_twentySixX_30738938986673378955295401620,
    phi_twentySixX_30738938986673378955295401621, phi_twentySixX_30738938986673378955295401622, phi_twentySixX_30738938986673378955295401623,
    phi_twentySixX_30738938986673378955295401624, phi_twentySixX_30738938986673378955295401625, phi_twentySixX_30738938986673378955295401626,
    phi_twentySixX_30738938986673378955295401627, phi_twentySixX_30738938986673378955295401628, phi_twentySixX_30738938986673378955295401629,
    phi_twentySixX_30738938986673378955295401630, phi_twentySixX_30738938986673378955295401631, phi_twentySixX_30738938986673378955295401632,
    phi_twentySixX_30738938986673378955295401633, phi_twentySixX_30738938986673378955295401634, phi_twentySixX_30738938986673378955295401635,
    phi_twentySixX_30738938986673378955295401636, phi_twentySixX_30738938986673378955295401637, phi_twentySixX_30738938986673378955295401638,
    phi_twentySixX_30738938986673378955295401639, phi_twentySixX_30738938986673378955295401640, phi_twentySixX_30738938986673378955295401641,
    phi_twentySixX_30738938986673378955295401642, phi_twentySixX_30738938986673378955295401643, phi_twentySixX_30738938986673378955295401644,
    phi_twentySixX_30738938986673378955295401645, phi_twentySixX_30738938986673378955295401646, phi_twentySixX_30738938986673378955295401647,
    phi_twentySixX_30738938986673378955295401648, phi_twentySixX_30738938986673378955295401649, phi_twentySixX_30738938986673378955295401650,
    phi_twentySixX_30738938986673378955295401651, phi_twentySixX_30738938986673378955295401652, phi_twentySixX_30738938986673378955295401653,
    phi_twentySixX_30738938986673378955295401654, phi_twentySixX_30738938986673378955295401655, phi_twentySixX_30738938986673378955295401656,
    phi_twentySixX_30738938986673378955295401657, phi_twentySixX_30738938986673378955295401658, phi_twentySixX_30738938986673378955295401659,
    phi_twentySixX_30738938986673378955295401660, phi_twentySixX_30738938986673378955295401661, phi_twentySixX_30738938986673378955295401662,
    phi_twentySixX_30738938986673378955295401663, phi_twentySixX_30738938986673378955295401664, phi_twentySixX_30738938986673378955295401665,
    phi_twentySixX_30738938986673378955295401666, phi_twentySixX_30738938986673378955295401667, phi_twentySixX_30738938986673378955295401668,
    phi_twentySixX_30738938986673378955295401669, phi_twentySixX_30738938986673378955295401670, phi_twentySixX_30738938986673378955295401671,
    phi_twentySixX_30738938986673378955295401672, phi_twentySixX_30738938986673378955295401673, phi_twentySixX_30738938986673378955295401674,
    phi_twentySixX_30738938986673378955295401675, phi_twentySixX_30738938986673378955295401676, phi_twentySixX_30738938986673378955295401677,
    phi_twentySixX_30738938986673378955295401678, phi_twentySixX_30738938986673378955295401679, phi_twentySixX_30738938986673378955295401680,
    phi_twentySixX_30738938986673378955295401681, phi_twentySixX_30738938986673378955295401682, phi_twentySixX_30738938986673378955295401683,
    phi_twentySixX_30738938986673378955295401684, phi_twentySixX_30738938986673378955295401685, phi_twentySixX_30738938986673378955295401686,
    phi_twentySixX_30738938986673378955295401687, phi_twentySixX_30738938986673378955295401688, phi_twentySixX_30738938986673378955295401689,
    phi_twentySixX_30738938986673378955295401690, phi_twentySixX_30738938986673378955295401691, phi_twentySixX_30738938986673378955295401692,
    phi_twentySixX_30738938986673378955295401693, phi_twentySixX_30738938986673378955295401694, phi_twentySixX_30738938986673378955295401695,
    phi_twentySixX_30738938986673378955295401696, phi_twentySixX_30738938986673378955295401697, phi_twentySixX_30738938986673378955295401698,
    phi_twentySixX_30738938986673378955295401699]

end TotientTailPeriodKiller
end Erdos249257
