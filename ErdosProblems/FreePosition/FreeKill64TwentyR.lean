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
  prime_t64_109
  prime_t64_113
  prime_t64_137
  prime_t64_139
  prime_t64_149
  prime_t64_157
  prime_t64_163
  prime_t64_167
  prime_t64_179
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_227
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_283
  prime_t64_317
  prime_t64_349
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_467
  prime_t64_491
  prime_t64_563
  prime_t64_617
  prime_t64_673
  prime_t64_761
  prime_t64_859
  prime_t64_1061
  prime_t64_1093
  prime_t64_1153
  prime_t64_1409
  prime_t64_1423
  prime_t64_1483
  prime_t64_1783
  prime_t64_2963
  prime_t64_4327
  prime_t64_5009
  prime_t64_97523
  prime_t64_210193
  prime_t64_1214459
  prime_t64_2072201
  prime_t64_2567179
  prime_t64_9492089
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private def twentyRFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyRFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyRFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyRFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyRFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyRFastPow a n * twentyRFastPow a n * a
        else twentyRFastPow a n * twentyRFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyR_131 : Nat.Prime 131 := by norm_num

private theorem prime_twentyR_151 : Nat.Prime 151 := by norm_num

private theorem prime_twentyR_173 : Nat.Prime 173 := by norm_num

private theorem prime_twentyR_181 : Nat.Prime 181 := by norm_num

private theorem prime_twentyR_199 : Nat.Prime 199 := by norm_num

private theorem prime_twentyR_211 : Nat.Prime 211 := by norm_num

private theorem prime_twentyR_241 : Nat.Prime 241 := by norm_num

private theorem prime_twentyR_257 : Nat.Prime 257 := by norm_num

private theorem prime_twentyR_271 : Nat.Prime 271 := by norm_num

private theorem prime_twentyR_281 : Nat.Prime 281 := by norm_num

private theorem prime_twentyR_347 : Nat.Prime 347 := by norm_num

private theorem prime_twentyR_353 : Nat.Prime 353 := by norm_num

private theorem prime_twentyR_373 : Nat.Prime 373 := by norm_num

private theorem prime_twentyR_397 : Nat.Prime 397 := by norm_num

private theorem prime_twentyR_401 : Nat.Prime 401 := by norm_num

private theorem prime_twentyR_443 : Nat.Prime 443 := by norm_num

private theorem prime_twentyR_449 : Nat.Prime 449 := by norm_num

private theorem prime_twentyR_457 : Nat.Prime 457 := by norm_num

private theorem prime_twentyR_463 : Nat.Prime 463 := by norm_num

private theorem prime_twentyR_509 : Nat.Prime 509 := by norm_num

private theorem prime_twentyR_523 : Nat.Prime 523 := by norm_num

private theorem prime_twentyR_541 : Nat.Prime 541 := by norm_num

private theorem prime_twentyR_569 : Nat.Prime 569 := by norm_num

private theorem prime_twentyR_599 : Nat.Prime 599 := by norm_num

private theorem prime_twentyR_613 : Nat.Prime 613 := by norm_num

private theorem prime_twentyR_619 : Nat.Prime 619 := by norm_num

private theorem prime_twentyR_631 : Nat.Prime 631 := by norm_num

private theorem prime_twentyR_653 : Nat.Prime 653 := by norm_num

private theorem prime_twentyR_659 : Nat.Prime 659 := by norm_num

private theorem prime_twentyR_733 : Nat.Prime 733 := by norm_num

private theorem prime_twentyR_739 : Nat.Prime 739 := by norm_num

private theorem prime_twentyR_809 : Nat.Prime 809 := by norm_num

private theorem prime_twentyR_829 : Nat.Prime 829 := by norm_num

private theorem prime_twentyR_887 : Nat.Prime 887 := by norm_num

private theorem prime_twentyR_937 : Nat.Prime 937 := by norm_num

private theorem prime_twentyR_947 : Nat.Prime 947 := by norm_num

private theorem prime_twentyR_977 : Nat.Prime 977 := by norm_num

private theorem prime_twentyR_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_twentyR_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_twentyR_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_twentyR_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_twentyR_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_twentyR_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_twentyR_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_twentyR_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_twentyR_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_twentyR_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_twentyR_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_twentyR_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_twentyR_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_twentyR_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_twentyR_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_twentyR_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_twentyR_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_twentyR_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_twentyR_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_twentyR_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_twentyR_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_twentyR_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_twentyR_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_twentyR_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_twentyR_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_twentyR_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_twentyR_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_twentyR_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_twentyR_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_twentyR_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_twentyR_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_twentyR_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_twentyR_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_twentyR_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_twentyR_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_twentyR_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_twentyR_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_twentyR_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_twentyR_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_twentyR_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_twentyR_3061 : Nat.Prime 3061 := by norm_num

private theorem prime_twentyR_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_twentyR_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_twentyR_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_twentyR_3371 : Nat.Prime 3371 := by norm_num

private theorem prime_twentyR_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_twentyR_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_twentyR_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_twentyR_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_twentyR_4483 : Nat.Prime 4483 := by norm_num

private theorem prime_twentyR_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_twentyR_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_twentyR_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_twentyR_5387 : Nat.Prime 5387 := by norm_num

private theorem prime_twentyR_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_twentyR_5563 : Nat.Prime 5563 := by norm_num

private theorem prime_twentyR_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_twentyR_5801 : Nat.Prime 5801 := by norm_num

private theorem prime_twentyR_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_twentyR_6029 : Nat.Prime 6029 := by norm_num

private theorem prime_twentyR_6067 : Nat.Prime 6067 := by norm_num

private theorem prime_twentyR_6121 : Nat.Prime 6121 := by norm_num

private theorem prime_twentyR_6529 : Nat.Prime 6529 := by norm_num

private theorem prime_twentyR_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_twentyR_6577 : Nat.Prime 6577 := by norm_num

private theorem prime_twentyR_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_twentyR_7489 : Nat.Prime 7489 := by norm_num

private theorem prime_twentyR_7507 : Nat.Prime 7507 := by norm_num

private theorem prime_twentyR_7841 : Nat.Prime 7841 := by norm_num

private theorem prime_twentyR_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_twentyR_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_twentyR_9221 : Nat.Prime 9221 := by norm_num

private theorem prime_twentyR_9257 : Nat.Prime 9257 := by norm_num

private theorem prime_twentyR_9461 : Nat.Prime 9461 := by norm_num

private theorem prime_twentyR_9473 : Nat.Prime 9473 := by norm_num

private theorem prime_twentyR_9497 : Nat.Prime 9497 := by norm_num

private theorem prime_twentyR_9739 : Nat.Prime 9739 := by norm_num

private theorem prime_twentyR_9871 : Nat.Prime 9871 := by norm_num

private theorem prime_twentyR_10099 : Nat.Prime 10099 := by norm_num

private theorem prime_twentyR_10303 : Nat.Prime 10303 := by norm_num

private theorem prime_twentyR_10567 : Nat.Prime 10567 := by norm_num

private theorem prime_twentyR_10687 : Nat.Prime 10687 := by norm_num

private theorem prime_twentyR_11069 : Nat.Prime 11069 := by norm_num

private theorem prime_twentyR_11177 : Nat.Prime 11177 := by norm_num

private theorem prime_twentyR_11197 : Nat.Prime 11197 := by norm_num

private theorem prime_twentyR_11443 : Nat.Prime 11443 := by norm_num

private theorem prime_twentyR_11779 : Nat.Prime 11779 := by norm_num

private theorem prime_twentyR_12097 : Nat.Prime 12097 := by norm_num

private theorem prime_twentyR_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_twentyR_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_twentyR_13297 : Nat.Prime 13297 := by norm_num

private theorem prime_twentyR_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_twentyR_14401 : Nat.Prime 14401 := by norm_num

private theorem prime_twentyR_14431 : Nat.Prime 14431 := by norm_num

private theorem prime_twentyR_15383 : Nat.Prime 15383 := by norm_num

private theorem prime_twentyR_15661 : Nat.Prime 15661 := by norm_num

private theorem prime_twentyR_17077 : Nat.Prime 17077 := by norm_num

private theorem prime_twentyR_18397 : Nat.Prime 18397 := by norm_num

private theorem prime_twentyR_18919 : Nat.Prime 18919 := by norm_num

private theorem prime_twentyR_18947 : Nat.Prime 18947 := by norm_num

private theorem prime_twentyR_18979 : Nat.Prime 18979 := by norm_num

private theorem prime_twentyR_19073 : Nat.Prime 19073 := by norm_num

private theorem prime_twentyR_19853 : Nat.Prime 19853 := by norm_num

private theorem prime_twentyR_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_twentyR_22397 : Nat.Prime 22397 := by norm_num

private theorem prime_twentyR_23911 : Nat.Prime 23911 := by norm_num

private theorem prime_twentyR_24793 : Nat.Prime 24793 := by norm_num

private theorem prime_twentyR_25579 : Nat.Prime 25579 := by norm_num

private theorem prime_twentyR_25867 : Nat.Prime 25867 := by norm_num

private theorem prime_twentyR_28031 : Nat.Prime 28031 := by norm_num

private theorem prime_twentyR_29021 : Nat.Prime 29021 := by norm_num

private theorem prime_twentyR_30113 : Nat.Prime 30113 := by norm_num

private theorem prime_twentyR_30671 : Nat.Prime 30671 := by norm_num

private theorem prime_twentyR_30871 : Nat.Prime 30871 := by norm_num

private theorem prime_twentyR_33091 : Nat.Prime 33091 := by norm_num

private theorem prime_twentyR_33809 : Nat.Prime 33809 := by norm_num

private theorem prime_twentyR_34367 : Nat.Prime 34367 := by norm_num

private theorem prime_twentyR_35573 : Nat.Prime 35573 := by norm_num

private theorem prime_twentyR_37039 : Nat.Prime 37039 := by norm_num

private theorem prime_twentyR_39607 : Nat.Prime 39607 := by norm_num

private theorem prime_twentyR_42337 : Nat.Prime 42337 := by norm_num

private theorem prime_twentyR_43151 : Nat.Prime 43151 := by norm_num

private theorem prime_twentyR_44647 : Nat.Prime 44647 := by norm_num

private theorem prime_twentyR_46681 : Nat.Prime 46681 := by norm_num

private theorem prime_twentyR_47857 : Nat.Prime 47857 := by norm_num

private theorem prime_twentyR_48383 : Nat.Prime 48383 := by norm_num

private theorem prime_twentyR_50101 : Nat.Prime 50101 := by norm_num

private theorem prime_twentyR_50261 : Nat.Prime 50261 := by norm_num

private theorem prime_twentyR_51949 : Nat.Prime 51949 := by norm_num

private theorem prime_twentyR_53269 : Nat.Prime 53269 := by norm_num

private theorem prime_twentyR_54421 : Nat.Prime 54421 := by norm_num

private theorem prime_twentyR_55001 : Nat.Prime 55001 := by norm_num

private theorem prime_twentyR_55663 : Nat.Prime 55663 := by norm_num

private theorem prime_twentyR_57689 : Nat.Prime 57689 := by norm_num

private theorem prime_twentyR_57853 : Nat.Prime 57853 := by norm_num

private theorem prime_twentyR_59659 : Nat.Prime 59659 := by norm_num

private theorem prime_twentyR_60427 : Nat.Prime 60427 := by norm_num

private theorem prime_twentyR_61379 : Nat.Prime 61379 := by norm_num

private theorem prime_twentyR_61553 : Nat.Prime 61553 := by norm_num

private theorem prime_twentyR_64153 : Nat.Prime 64153 := by norm_num

private theorem prime_twentyR_69191 : Nat.Prime 69191 := by norm_num

private theorem prime_twentyR_73547 : Nat.Prime 73547 := by norm_num

private theorem prime_twentyR_73771 : Nat.Prime 73771 := by norm_num

private theorem prime_twentyR_76001 : Nat.Prime 76001 := by norm_num

private theorem prime_twentyR_76343 : Nat.Prime 76343 := by norm_num

private theorem prime_twentyR_82267 : Nat.Prime 82267 := by norm_num

private theorem prime_twentyR_85303 : Nat.Prime 85303 := by norm_num

private theorem prime_twentyR_86353 : Nat.Prime 86353 := by norm_num

private theorem prime_twentyR_93287 : Nat.Prime 93287 := by norm_num

private theorem prime_twentyR_95929 : Nat.Prime 95929 := by norm_num

private theorem prime_twentyR_97387 : Nat.Prime 97387 := by norm_num

private theorem prime_twentyR_98507 : Nat.Prime 98507 := by norm_num

private theorem prime_twentyR_98711 : Nat.Prime 98711 := by norm_num

private theorem prime_twentyR_99611 : Nat.Prime 99611 := by norm_num

private theorem prime_twentyR_101287 : Nat.Prime 101287 := by norm_num

private theorem prime_twentyR_108631 : Nat.Prime 108631 := by norm_num

private theorem prime_twentyR_111509 : Nat.Prime 111509 := by norm_num

private theorem prime_twentyR_114997 : Nat.Prime 114997 := by norm_num

private theorem prime_twentyR_119557 : Nat.Prime 119557 := by norm_num

private theorem prime_twentyR_119881 : Nat.Prime 119881 := by norm_num

private theorem prime_twentyR_123401 : Nat.Prime 123401 := by norm_num

private theorem prime_twentyR_124459 : Nat.Prime 124459 := by norm_num

private theorem prime_twentyR_131371 : Nat.Prime 131371 := by norm_num

private theorem prime_twentyR_141613 : Nat.Prime 141613 := by norm_num

private theorem prime_twentyR_143669 : Nat.Prime 143669 := by norm_num

private theorem prime_twentyR_150571 : Nat.Prime 150571 := by norm_num

private theorem prime_twentyR_156521 : Nat.Prime 156521 := by norm_num

private theorem prime_twentyR_157291 : Nat.Prime 157291 := by norm_num

private theorem prime_twentyR_163987 : Nat.Prime 163987 := by norm_num

private theorem prime_twentyR_170447 : Nat.Prime 170447 := by norm_num

private theorem prime_twentyR_171793 : Nat.Prime 171793 := by norm_num

private theorem prime_twentyR_177409 : Nat.Prime 177409 := by norm_num

private theorem prime_twentyR_182929 : Nat.Prime 182929 := by norm_num

private theorem prime_twentyR_196271 : Nat.Prime 196271 := by norm_num

private theorem prime_twentyR_210961 : Nat.Prime 210961 := by norm_num

private theorem prime_twentyR_225749 : Nat.Prime 225749 := by norm_num

private theorem prime_twentyR_242989 : Nat.Prime 242989 := by norm_num

private theorem prime_twentyR_260329 : Nat.Prime 260329 := by norm_num

private theorem prime_twentyR_263761 : Nat.Prime 263761 := by norm_num

private theorem prime_twentyR_284777 : Nat.Prime 284777 := by norm_num

private theorem prime_twentyR_287801 : Nat.Prime 287801 := by norm_num

private theorem prime_twentyR_342239 : Nat.Prime 342239 := by norm_num

private theorem prime_twentyR_352409 : Nat.Prime 352409 := by norm_num

private theorem prime_twentyR_374681 : Nat.Prime 374681 := by norm_num

private theorem prime_twentyR_381559 : Nat.Prime 381559 := by norm_num

private theorem prime_twentyR_382747 : Nat.Prime 382747 := by norm_num

private theorem prime_twentyR_384973 : Nat.Prime 384973 := by norm_num

private theorem prime_twentyR_396631 : Nat.Prime 396631 := by norm_num

private theorem prime_twentyR_492979 : Nat.Prime 492979 := by norm_num

private theorem prime_twentyR_501037 : Nat.Prime 501037 := by norm_num

private theorem prime_twentyR_505097 : Nat.Prime 505097 := by norm_num

private theorem prime_twentyR_558757 : Nat.Prime 558757 := by norm_num

private theorem prime_twentyR_596369 : Nat.Prime 596369 := by norm_num

private theorem prime_twentyR_599399 : Nat.Prime 599399 := by norm_num

private theorem prime_twentyR_609781 : Nat.Prime 609781 := by norm_num

private theorem prime_twentyR_615493 : Nat.Prime 615493 := by norm_num

private theorem prime_twentyR_641057 : Nat.Prime 641057 := by norm_num

private theorem prime_twentyR_655559 : Nat.Prime 655559 := by norm_num

private theorem prime_twentyR_656951 : Nat.Prime 656951 := by norm_num

private theorem prime_twentyR_762563 : Nat.Prime 762563 := by norm_num

private theorem prime_twentyR_798923 : Nat.Prime 798923 := by norm_num

private theorem prime_twentyR_806041 : Nat.Prime 806041 := by norm_num

private theorem prime_twentyR_827303 : Nat.Prime 827303 := by norm_num

private theorem prime_twentyR_872203 : Nat.Prime 872203 := by norm_num

private theorem prime_twentyR_874459 : Nat.Prime 874459 := by norm_num

private theorem prime_twentyR_906371 : Nat.Prime 906371 := by norm_num

private theorem prime_twentyR_1025231 : Nat.Prime 1025231 := by norm_num

private theorem prime_twentyR_1044397 : Nat.Prime 1044397 := by norm_num

private theorem prime_twentyR_1217921 : Nat.Prime 1217921 := by norm_num

private theorem prime_twentyR_1278733 : Nat.Prime 1278733 := by norm_num

private theorem prime_twentyR_1309793 : Nat.Prime 1309793 := by norm_num

private theorem prime_twentyR_1314539 : Nat.Prime 1314539 := by norm_num

private theorem prime_twentyR_1363189 : Nat.Prime 1363189 := by norm_num

private theorem prime_twentyR_1433741 : Nat.Prime 1433741 := by norm_num

private theorem prime_twentyR_1479571 : Nat.Prime 1479571 := by norm_num

private theorem prime_twentyR_1544987 : Nat.Prime 1544987 := by norm_num

private theorem prime_twentyR_1719547 : Nat.Prime 1719547 := by norm_num

private theorem prime_twentyR_1750447 : Nat.Prime 1750447 := by norm_num

private theorem prime_twentyR_2017843 : Nat.Prime 2017843 := by norm_num

private theorem prime_twentyR_2036459 : Nat.Prime 2036459 := by norm_num

private theorem prime_twentyR_2098079 : Nat.Prime 2098079 := by norm_num

private theorem prime_twentyR_2106383 : Nat.Prime 2106383 := by norm_num

private theorem prime_twentyR_2122619 : Nat.Prime 2122619 := by norm_num

private theorem prime_twentyR_2227409 : Nat.Prime 2227409 := by norm_num

private theorem prime_twentyR_2409709 : Nat.Prime 2409709 := by norm_num

private theorem prime_twentyR_2411737 : Nat.Prime 2411737 := by norm_num

private theorem prime_twentyR_2428859 : Nat.Prime 2428859 := by norm_num

private theorem prime_twentyR_2669767 : Nat.Prime 2669767 := by norm_num

private theorem prime_twentyR_2685877 : Nat.Prime 2685877 := by norm_num

private theorem prime_twentyR_3035453 : Nat.Prime 3035453 := by norm_num

private theorem prime_twentyR_3073999 : Nat.Prime 3073999 := by norm_num

private theorem prime_twentyR_3421567 : Nat.Prime 3421567 := by norm_num

private theorem prime_twentyR_3439229 : Nat.Prime 3439229 := by norm_num

private theorem prime_twentyR_3477841 : Nat.Prime 3477841 := by norm_num

private theorem prime_twentyR_3509741 : Nat.Prime 3509741 := by norm_num

private theorem prime_twentyR_3539743 : Nat.Prime 3539743 := by norm_num

private theorem prime_twentyR_3572203 : Nat.Prime 3572203 := by norm_num

private theorem prime_twentyR_3586771 : Nat.Prime 3586771 := by norm_num

private theorem prime_twentyR_4267007 : Nat.Prime 4267007 := by norm_num

private theorem prime_twentyR_4988569 : Nat.Prime 4988569 := by norm_num

private theorem prime_twentyR_5075167 : Nat.Prime 5075167 := by norm_num

private theorem prime_twentyR_5462683 : Nat.Prime 5462683 := by norm_num

private theorem prime_twentyR_6100169 : Nat.Prime 6100169 := by norm_num

private theorem prime_twentyR_6246199 : Nat.Prime 6246199 := by norm_num

private theorem prime_twentyR_6512609 : Nat.Prime 6512609 := by norm_num

private theorem prime_twentyR_6514591 : Nat.Prime 6514591 := by norm_num

private theorem prime_twentyR_7116059 : Nat.Prime 7116059 := by norm_num

private theorem prime_twentyR_7220867 : Nat.Prime 7220867 := by norm_num

private theorem prime_twentyR_7294097 : Nat.Prime 7294097 := by norm_num

private theorem prime_twentyR_9813829 : Nat.Prime 9813829 := by norm_num

private theorem prime_twentyR_10105057 : Nat.Prime 10105057 := by
  apply lucas_primality 10105057 (15 : ZMod 10105057)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (13, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (13, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) = 10105057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyR_2699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 10105057) ^ 5052528 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 10105057) ^ 3368352 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 10105057) ^ 777312 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 10105057) ^ 3744 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10125847 : Nat.Prime 10125847 := by
  apply lucas_primality 10125847 (5 : ZMod 10125847)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (33091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (33091, 1)] : List FactorBlock).map factorBlockValue).prod) = 10125847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_33091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10125847) ^ 5062923 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10125847) ^ 3375282 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10125847) ^ 595638 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10125847) ^ 306 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_11637001 : Nat.Prime 11637001 := by
  apply lucas_primality 11637001 (7 : ZMod 11637001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 3), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 3), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 11637001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 11637001) ^ 5818500 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11637001) ^ 3879000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11637001) ^ 2327400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11637001) ^ 27000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_12826067 : Nat.Prime 12826067 := by
  apply lucas_primality 12826067 (2 : ZMod 12826067)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (179, 1), (3257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (179, 1), (3257, 1)] : List FactorBlock).map factorBlockValue).prod) = 12826067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_179
      · exact prime_twentyR_3257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12826067) ^ 6413033 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12826067) ^ 1166006 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12826067) ^ 71654 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12826067) ^ 3938 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_13025219 : Nat.Prime 13025219 := by
  apply lucas_primality 13025219 (2 : ZMod 13025219)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6512609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6512609, 1)] : List FactorBlock).map factorBlockValue).prod) = 13025219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_6512609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13025219) ^ 6512609 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13025219) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_13737811 : Nat.Prime 13737811 := by
  apply lucas_primality 13737811 (3 : ZMod 13737811)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) = 13737811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_twentyR_7507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13737811) ^ 6868905 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 4579270 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 2747562 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 225210 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 1830 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_14719189 : Nat.Prime 14719189 := by
  apply lucas_primality 14719189 (6 : ZMod 14719189)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (111509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (111509, 1)] : List FactorBlock).map factorBlockValue).prod) = 14719189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyR_111509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14719189) ^ 7359594 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 4906396 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 1338108 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 132 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_15558227 : Nat.Prime 15558227 := by
  apply lucas_primality 15558227 (2 : ZMod 15558227)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (383, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (383, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 15558227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_383
      · exact prime_twentyR_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15558227) ^ 7779113 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 818854 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 40622 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 14554 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_16152949 : Nat.Prime 16152949 := by
  apply lucas_primality 16152949 (2 : ZMod 16152949)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) = 16152949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyR_9157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16152949) ^ 8076474 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16152949) ^ 5384316 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16152949) ^ 2307564 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16152949) ^ 1764 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_18337103 : Nat.Prime 18337103 := by
  apply lucas_primality 18337103 (5 : ZMod 18337103)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1309793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1309793, 1)] : List FactorBlock).map factorBlockValue).prod) = 18337103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_1309793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18337103) ^ 9168551 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 18337103) ^ 2619586 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 18337103) ^ 14 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_18510553 : Nat.Prime 18510553 := by
  apply lucas_primality 18510553 (5 : ZMod 18510553)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (17, 1), (71, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (17, 1), (71, 2)] : List FactorBlock).map factorBlockValue).prod) = 18510553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_71
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18510553) ^ 9255276 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 18510553) ^ 6170184 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 18510553) ^ 1088856 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 18510553) ^ 260712 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_20323781 : Nat.Prime 20323781 := by
  apply lucas_primality 20323781 (2 : ZMod 20323781)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (67, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (67, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 20323781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_t64_67
      · exact prime_twentyR_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20323781) ^ 10161890 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20323781) ^ 4064756 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20323781) ^ 700820 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20323781) ^ 303340 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20323781) ^ 38860 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_21346979 : Nat.Prime 21346979 := by
  apply lucas_primality 21346979 (2 : ZMod 21346979)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 21346979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_twentyR_260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21346979) ^ 10673489 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 21346979) ^ 520658 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 21346979) ^ 82 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_21560909 : Nat.Prime 21560909 := by
  apply lucas_primality 21560909 (2 : ZMod 21560909)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (30113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (30113, 1)] : List FactorBlock).map factorBlockValue).prod) = 21560909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_179
      · exact prime_twentyR_30113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21560909) ^ 10780454 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 21560909) ^ 120452 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 21560909) ^ 716 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_21850733 : Nat.Prime 21850733 := by
  apply lucas_primality 21850733 (2 : ZMod 21850733)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5462683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5462683, 1)] : List FactorBlock).map factorBlockValue).prod) = 21850733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_5462683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21850733) ^ 10925366 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 21850733) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_23622671 : Nat.Prime 23622671 := by
  apply lucas_primality 23622671 (7 : ZMod 23622671)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (50261, 1)] : List FactorBlock).map factorBlockValue).prod) = 23622671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_47
      · exact prime_twentyR_50261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23622671) ^ 11811335 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 4724534 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 502610 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 470 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_26984483 : Nat.Prime 26984483 := by
  apply lucas_primality 26984483 (2 : ZMod 26984483)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1291, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1291, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 26984483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_1291
      · exact prime_twentyR_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26984483) ^ 13492241 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26984483) ^ 3854926 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26984483) ^ 20902 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26984483) ^ 18074 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_27147583 : Nat.Prime 27147583 := by
  apply lucas_primality 27147583 (5 : ZMod 27147583)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (11, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (11, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) = 27147583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyR_6529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27147583) ^ 13573791 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 27147583) ^ 9049194 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 27147583) ^ 3878226 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 27147583) ^ 2467962 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 27147583) ^ 4158 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_27212041 : Nat.Prime 27212041 := by
  apply lucas_primality 27212041 (7 : ZMod 27212041)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (269, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (269, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 27212041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_269
      · exact prime_twentyR_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27212041) ^ 13606020 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 9070680 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 5442408 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 101160 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 27212041) ^ 96840 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_28484437 : Nat.Prime 28484437 := by
  apply lucas_primality 28484437 (6 : ZMod 28484437)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) = 28484437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_139
      · exact prime_twentyR_17077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 28484437) ^ 14242218 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 28484437) ^ 9494812 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 28484437) ^ 204924 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 28484437) ^ 1668 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_29654903 : Nat.Prime 29654903 := by
  apply lucas_primality 29654903 (10 : ZMod 29654903)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (872203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (872203, 1)] : List FactorBlock).map factorBlockValue).prod) = 29654903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyR_872203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 29654903) ^ 14827451 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 29654903) ^ 1744406 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 29654903) ^ 34 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_30083567 : Nat.Prime 30083567 := by
  apply lucas_primality 30083567 (5 : ZMod 30083567)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1277, 1), (11779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1277, 1), (11779, 1)] : List FactorBlock).map factorBlockValue).prod) = 30083567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1277
      · exact prime_twentyR_11779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30083567) ^ 15041783 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 30083567) ^ 23558 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 30083567) ^ 2554 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_30126293 : Nat.Prime 30126293 := by
  apply lucas_primality 30126293 (2 : ZMod 30126293)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (109, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) = 30126293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_109
      · exact prime_twentyR_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30126293) ^ 15063146 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 4303756 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 276388 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30126293) ^ 3052 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_32364193 : Nat.Prime 32364193 := by
  apply lucas_primality 32364193 (15 : ZMod 32364193)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32364193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_twentyR_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32364193) ^ 16182096 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 10788064 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 4623456 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 1903776 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 11424 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_36960233 : Nat.Prime 36960233 := by
  apply lucas_primality 36960233 (3 : ZMod 36960233)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (55663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (55663, 1)] : List FactorBlock).map factorBlockValue).prod) = 36960233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_83
      · exact prime_twentyR_55663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36960233) ^ 18480116 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36960233) ^ 445304 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36960233) ^ 664 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_37980161 : Nat.Prime 37980161 := by
  apply lucas_primality 37980161 (3 : ZMod 37980161)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (5, 1), (3709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (5, 1), (3709, 1)] : List FactorBlock).map factorBlockValue).prod) = 37980161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_3709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37980161) ^ 18990080 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37980161) ^ 7596032 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37980161) ^ 10240 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_40908451 : Nat.Prime 40908451 := by
  apply lucas_primality 40908451 (2 : ZMod 40908451)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (24793, 1)] : List FactorBlock).map factorBlockValue).prod) = 40908451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentyR_24793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40908451) ^ 20454225 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 13636150 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 8181690 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 3718950 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40908451) ^ 1650 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_41734093 : Nat.Prime 41734093 := by
  apply lucas_primality 41734093 (2 : ZMod 41734093)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod) = 41734093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41734093) ^ 20867046 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 13911364 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41734093) ^ 12 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_43393043 : Nat.Prime 43393043 := by
  apply lucas_primality 43393043 (2 : ZMod 43393043)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (23, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (23, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) = 43393043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentyR_12251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43393043) ^ 21696521 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 6199006 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 3944822 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 1886654 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43393043) ^ 3542 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_46098109 : Nat.Prime 46098109 := by
  apply lucas_primality 46098109 (14 : ZMod 46098109)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (182929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (182929, 1)] : List FactorBlock).map factorBlockValue).prod) = 46098109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyR_182929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 46098109) ^ 23049054 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 46098109) ^ 15366036 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 46098109) ^ 6585444 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 46098109) ^ 252 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_52023863 : Nat.Prime 52023863 := by
  apply lucas_primality 52023863 (5 : ZMod 52023863)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (124459, 1)] : List FactorBlock).map factorBlockValue).prod) = 52023863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_twentyR_124459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52023863) ^ 26011931 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 4729442 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 2738098 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 52023863) ^ 418 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_56297287 : Nat.Prime 56297287 := by
  apply lucas_primality 56297287 (3 : ZMod 56297287)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) = 56297287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_twentyR_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56297287) ^ 28148643 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 18765762 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 840258 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 56297287) ^ 1206 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_56624411 : Nat.Prime 56624411 := by
  apply lucas_primality 56624411 (2 : ZMod 56624411)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (51949, 1)] : List FactorBlock).map factorBlockValue).prod) = 56624411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_109
      · exact prime_twentyR_51949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56624411) ^ 28312205 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 11324882 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 519490 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56624411) ^ 1090 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_57889883 : Nat.Prime 57889883 := by
  apply lucas_primality 57889883 (2 : ZMod 57889883)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (353, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (353, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 57889883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_167
      · exact prime_twentyR_353
      · exact prime_t64_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57889883) ^ 28944941 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 346646 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 163994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57889883) ^ 117902 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_59738099 : Nat.Prime 59738099 := by
  apply lucas_primality 59738099 (2 : ZMod 59738099)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4267007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4267007, 1)] : List FactorBlock).map factorBlockValue).prod) = 59738099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_4267007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59738099) ^ 29869049 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59738099) ^ 8534014 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59738099) ^ 14 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_62461991 : Nat.Prime 62461991 := by
  apply lucas_primality 62461991 (7 : ZMod 62461991)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6246199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6246199, 1)] : List FactorBlock).map factorBlockValue).prod) = 62461991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_6246199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 62461991) ^ 31230995 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62461991) ^ 12492398 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62461991) ^ 10 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_62963231 : Nat.Prime 62963231 := by
  apply lucas_primality 62963231 (7 : ZMod 62963231)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (73, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (73, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) = 62963231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_73
      · exact prime_twentyR_7841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62963231) ^ 31481615 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 12592646 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 5723930 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 862510 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 62963231) ^ 8030 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_64144099 : Nat.Prime 64144099 := by
  apply lucas_primality 64144099 (2 : ZMod 64144099)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (71, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 64144099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_t64_71
      · exact prime_twentyR_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64144099) ^ 32072049 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 21381366 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 1210266 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 903438 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 64144099) ^ 67734 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_66552427 : Nat.Prime 66552427 := by
  apply lucas_primality 66552427 (2 : ZMod 66552427)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1427, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1427, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) = 66552427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_1427
      · exact prime_twentyR_2591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66552427) ^ 33276213 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 22184142 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 46638 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66552427) ^ 25686 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1901
      · exact prime_twentyR_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_74258111 : Nat.Prime 74258111 := by
  apply lucas_primality 74258111 (7 : ZMod 74258111)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67, 1), (137, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67, 1), (137, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 74258111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_67
      · exact prime_t64_137
      · exact prime_twentyR_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 74258111) ^ 37129055 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 74258111) ^ 14851622 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 74258111) ^ 1108330 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 74258111) ^ 542030 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 74258111) ^ 91790 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_78786709 : Nat.Prime 78786709 := by
  apply lucas_primality 78786709 (6 : ZMod 78786709)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 1), (13, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 78786709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentyR_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 78786709) ^ 39393354 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 26262236 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 11255244 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 7162428 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 6060516 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 78786709) ^ 84084 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_82478129 : Nat.Prime 82478129 := by
  apply lucas_primality 82478129 (3 : ZMod 82478129)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (119881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (119881, 1)] : List FactorBlock).map factorBlockValue).prod) = 82478129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_twentyR_119881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 82478129) ^ 41239064 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 82478129) ^ 1918096 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 82478129) ^ 688 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_86786087 : Nat.Prime 86786087 := by
  apply lucas_primality 86786087 (5 : ZMod 86786087)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43393043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43393043, 1)] : List FactorBlock).map factorBlockValue).prod) = 86786087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_43393043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 86786087) ^ 43393043 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 86786087) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_twentyR_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_102452173 : Nat.Prime 102452173 := by
  apply lucas_primality 102452173 (2 : ZMod 102452173)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (95929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (95929, 1)] : List FactorBlock).map factorBlockValue).prod) = 102452173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_twentyR_95929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102452173) ^ 51226086 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452173) ^ 34150724 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452173) ^ 1151148 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452173) ^ 1068 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_105801979 : Nat.Prime 105801979 := by
  apply lucas_primality 105801979 (3 : ZMod 105801979)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 105801979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_67
      · exact prime_twentyR_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105801979) ^ 52900989 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 35267326 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 4600086 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 1579134 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105801979) ^ 9246 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_twentyR_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_110421277 : Nat.Prime 110421277 := by
  apply lucas_primality 110421277 (2 : ZMod 110421277)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1314539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1314539, 1)] : List FactorBlock).map factorBlockValue).prod) = 110421277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyR_1314539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110421277) ^ 55210638 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 36807092 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 15774468 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 110421277) ^ 84 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_113937749 : Nat.Prime 113937749 := by
  apply lucas_primality 113937749 (2 : ZMod 113937749)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (28484437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (28484437, 1)] : List FactorBlock).map factorBlockValue).prod) = 113937749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_28484437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 113937749) ^ 56968874 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 113937749) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_115779767 : Nat.Prime 115779767 := by
  apply lucas_primality 115779767 (5 : ZMod 115779767)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57889883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57889883, 1)] : List FactorBlock).map factorBlockValue).prod) = 115779767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_57889883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 115779767) ^ 57889883 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 115779767) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_126881009 : Nat.Prime 126881009 := by
  apply lucas_primality 126881009 (3 : ZMod 126881009)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) = 126881009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_73
      · exact prime_twentyR_108631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126881009) ^ 63440504 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126881009) ^ 1738096 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126881009) ^ 1168 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_130029563 : Nat.Prime 130029563 := by
  apply lucas_primality 130029563 (2 : ZMod 130029563)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (31, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (31, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) = 130029563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_twentyR_5563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130029563) ^ 65014781 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 130029563) ^ 10002274 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 130029563) ^ 4483778 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 130029563) ^ 4194502 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 130029563) ^ 23374 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_135170359 : Nat.Prime 135170359 := by
  apply lucas_primality 135170359 (6 : ZMod 135170359)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135170359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_t64_163
      · exact prime_twentyR_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135170359) ^ 67585179 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 45056786 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 3296838 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 829266 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 40098 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_143826233 : Nat.Prime 143826233 := by
  apply lucas_primality 143826233 (3 : ZMod 143826233)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 143826233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_563
      · exact prime_twentyR_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 143826233) ^ 71913116 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 13075112 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 255464 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 143826233) ^ 49544 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_152255011 : Nat.Prime 152255011 := by
  apply lucas_primality 152255011 (3 : ZMod 152255011)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5075167, 1)] : List FactorBlock).map factorBlockValue).prod) = 152255011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_5075167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152255011) ^ 76127505 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 50751670 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30451002 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 152255011) ^ 30 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_153704071 : Nat.Prime 153704071 := by
  apply lucas_primality 153704071 (29 : ZMod 153704071)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (131371, 1)] : List FactorBlock).map factorBlockValue).prod) = 153704071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyR_131371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 153704071) ^ 76852035 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (29 : ZMod 153704071) ^ 51234690 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (29 : ZMod 153704071) ^ 30740814 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (29 : ZMod 153704071) ^ 11823390 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (29 : ZMod 153704071) ^ 1170 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_163646341 : Nat.Prime 163646341 := by
  apply lucas_primality 163646341 (7 : ZMod 163646341)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) = 163646341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentyR_19073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163646341) ^ 81823170 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 54548780 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 32729268 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 14876940 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 12588180 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 8580 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_167470561 : Nat.Prime 167470561 := by
  apply lucas_primality 167470561 (13 : ZMod 167470561)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 167470561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_twentyR_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167470561) ^ 83735280 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 55823520 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 33494112 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 8814240 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 27360 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_183514301 : Nat.Prime 183514301 := by
  apply lucas_primality 183514301 (2 : ZMod 183514301)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (97, 1), (18919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (97, 1), (18919, 1)] : List FactorBlock).map factorBlockValue).prod) = 183514301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_97
      · exact prime_twentyR_18919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183514301) ^ 91757150 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 36702860 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 1891900 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 183514301) ^ 9700 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_193301777 : Nat.Prime 193301777 := by
  apply lucas_primality 193301777 (3 : ZMod 193301777)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (431, 1), (28031, 1)] : List FactorBlock).map factorBlockValue).prod) = 193301777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_431
      · exact prime_twentyR_28031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193301777) ^ 96650888 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 448496 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 193301777) ^ 6896 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_200447861 : Nat.Prime 200447861 := by
  apply lucas_primality 200447861 (2 : ZMod 200447861)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (271, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (271, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 200447861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_twentyR_271
      · exact prime_twentyR_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 200447861) ^ 100223930 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 40089572 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 6466060 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 739660 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 200447861) ^ 168020 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_205039441 : Nat.Prime 205039441 := by
  apply lucas_primality 205039441 (7 : ZMod 205039441)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (284777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (284777, 1)] : List FactorBlock).map factorBlockValue).prod) = 205039441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_284777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 205039441) ^ 102519720 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 205039441) ^ 68346480 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 205039441) ^ 41007888 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 205039441) ^ 720 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_222943571 : Nat.Prime 222943571 := by
  apply lucas_primality 222943571 (10 : ZMod 222943571)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (271, 1), (82267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (271, 1), (82267, 1)] : List FactorBlock).map factorBlockValue).prod) = 222943571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_271
      · exact prime_twentyR_82267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 222943571) ^ 111471785 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 222943571) ^ 44588714 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 222943571) ^ 822670 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 222943571) ^ 2710 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_225273263 : Nat.Prime 225273263 := by
  apply lucas_primality 225273263 (5 : ZMod 225273263)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (505097, 1)] : List FactorBlock).map factorBlockValue).prod) = 225273263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_223
      · exact prime_twentyR_505097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225273263) ^ 112636631 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 1010194 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 225273263) ^ 446 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (97, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 247757789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_97
      · exact prime_t64_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247757789) ^ 123878894 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_67
      · exact prime_twentyR_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_370747939 : Nat.Prime 370747939 := by
  apply lucas_primality 370747939 (2 : ZMod 370747939)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (47, 1), (107, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (47, 1), (107, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 370747939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_47
      · exact prime_t64_107
      · exact prime_twentyR_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 370747939) ^ 185373969 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 370747939) ^ 123582646 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 370747939) ^ 33704358 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 370747939) ^ 7888254 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 370747939) ^ 3464934 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 370747939) ^ 331914 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_381624127 : Nat.Prime 381624127 := by
  apply lucas_primality 381624127 (3 : ZMod 381624127)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (287801, 1)] : List FactorBlock).map factorBlockValue).prod) = 381624127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_twentyR_287801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 381624127) ^ 190812063 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 127208042 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 29355702 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 22448478 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381624127) ^ 1326 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_417616597 : Nat.Prime 417616597 := by
  apply lucas_primality 417616597 (2 : ZMod 417616597)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1549, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1549, 1), (7489, 1)] : List FactorBlock).map factorBlockValue).prod) = 417616597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_1549
      · exact prime_twentyR_7489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 417616597) ^ 208808298 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 139205532 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 269604 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 417616597) ^ 55764 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_426097523 : Nat.Prime 426097523 := by
  apply lucas_primality 426097523 (2 : ZMod 426097523)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1117, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) = 426097523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_twentyR_1117
      · exact prime_twentyR_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 426097523) ^ 213048761 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 14693018 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 381466 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 426097523) ^ 64786 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_433014277 : Nat.Prime 433014277 := by
  apply lucas_primality 433014277 (5 : ZMod 433014277)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2122619, 1)] : List FactorBlock).map factorBlockValue).prod) = 433014277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_2122619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433014277) ^ 216507138 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 144338092 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 25471428 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 433014277) ^ 204 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_490901413 : Nat.Prime 490901413 := by
  apply lucas_primality 490901413 (5 : ZMod 490901413)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40908451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40908451, 1)] : List FactorBlock).map factorBlockValue).prod) = 490901413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_40908451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 490901413) ^ 245450706 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 490901413) ^ 163633804 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 490901413) ^ 12 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (14719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 500452427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyR_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_503705849 : Nat.Prime 503705849 := by
  apply lucas_primality 503705849 (3 : ZMod 503705849)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (62963231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (62963231, 1)] : List FactorBlock).map factorBlockValue).prod) = 503705849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_62963231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 503705849) ^ 251852924 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 503705849) ^ 8 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_522823519 : Nat.Prime 522823519 := by
  apply lucas_primality 522823519 (6 : ZMod 522823519)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (73, 1), (18947, 1)] : List FactorBlock).map factorBlockValue).prod) = 522823519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_73
      · exact prime_twentyR_18947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 522823519) ^ 261411759 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 174274506 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 74689074 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 7161966 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 522823519) ^ 27594 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_569284721 : Nat.Prime 569284721 := by
  apply lucas_primality 569284721 (3 : ZMod 569284721)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7116059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7116059, 1)] : List FactorBlock).map factorBlockValue).prod) = 569284721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_7116059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 569284721) ^ 284642360 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 569284721) ^ 113856944 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 569284721) ^ 80 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_659006597 : Nat.Prime 659006597 := by
  apply lucas_primality 659006597 (2 : ZMod 659006597)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (641057, 1)] : List FactorBlock).map factorBlockValue).prod) = 659006597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_257
      · exact prime_twentyR_641057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 659006597) ^ 329503298 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 2564228 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 659006597) ^ 1028 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_889647091 : Nat.Prime 889647091 := by
  apply lucas_primality 889647091 (3 : ZMod 889647091)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) = 889647091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_29654903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 889647091) ^ 444823545 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 296549030 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 177929418 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 30 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_928715773 : Nat.Prime 928715773 := by
  apply lucas_primality 928715773 (2 : ZMod 928715773)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (673, 1), (114997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (673, 1), (114997, 1)] : List FactorBlock).map factorBlockValue).prod) = 928715773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_673
      · exact prime_twentyR_114997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 928715773) ^ 464357886 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 309571924 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 1379964 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 928715773) ^ 8076 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1087747789 : Nat.Prime 1087747789 := by
  apply lucas_primality 1087747789 (2 : ZMod 1087747789)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (401, 1), (13297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1087747789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_401
      · exact prime_twentyR_13297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1087747789) ^ 543873894 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 362582596 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 63985164 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 2712588 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1087747789) ^ 81804 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1113905813 : Nat.Prime 1113905813 := by
  apply lucas_primality 1113905813 (2 : ZMod 1113905813)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1621, 1), (171793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1621, 1), (171793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113905813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1621
      · exact prime_twentyR_171793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1113905813) ^ 556952906 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113905813) ^ 687172 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113905813) ^ 6484 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1223641049 : Nat.Prime 1223641049 := by
  apply lucas_primality 1223641049 (3 : ZMod 1223641049)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (21850733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (21850733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1223641049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_21850733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1223641049) ^ 611820524 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223641049) ^ 174805864 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223641049) ^ 56 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_59
      · exact prime_twentyR_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_twentyR_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1526496509 : Nat.Prime 1526496509 := by
  apply lucas_primality 1526496509 (2 : ZMod 1526496509)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (381624127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1526496509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_381624127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1526496509) ^ 763248254 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526496509) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1597258249 : Nat.Prime 1597258249 := by
  apply lucas_primality 1597258249 (7 : ZMod 1597258249)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (66552427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (66552427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597258249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_66552427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1597258249) ^ 798629124 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1597258249) ^ 532419416 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1597258249) ^ 24 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409, 1), (443, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1671268889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_409
      · exact prime_twentyR_443
      · exact prime_t64_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1944606701 : Nat.Prime 1944606701 := by
  apply lucas_primality 1944606701 (2 : ZMod 1944606701)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (197, 1), (98711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (197, 1), (98711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1944606701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_197
      · exact prime_twentyR_98711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1944606701) ^ 972303350 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944606701) ^ 388921340 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944606701) ^ 9871100 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1944606701) ^ 19700 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_twentyR_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2184771991 : Nat.Prime 2184771991 := by
  apply lucas_primality 2184771991 (6 : ZMod 2184771991)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (463, 1), (157291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (463, 1), (157291, 1)] : List FactorBlock).map factorBlockValue).prod) = 2184771991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_463
      · exact prime_twentyR_157291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2184771991) ^ 1092385995 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2184771991) ^ 728257330 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2184771991) ^ 436954398 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2184771991) ^ 4718730 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2184771991) ^ 13890 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2227811627 : Nat.Prime 2227811627 := by
  apply lucas_primality 2227811627 (2 : ZMod 2227811627)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1113905813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1113905813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2227811627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1113905813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2227811627) ^ 1113905813 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2227811627) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2267800291 : Nat.Prime 2267800291 := by
  apply lucas_primality 2267800291 (26 : ZMod 2267800291)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (29, 1), (47, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267800291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_29
      · exact prime_t64_47
      · exact prime_t64_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 2267800291) ^ 1133900145 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 755933430 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 453560058 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 323971470 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 119357910 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 78200010 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 48251070 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 2267800291) ^ 16315110 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_twentyR_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2628498527 : Nat.Prime 2628498527 := by
  apply lucas_primality 2628498527 (5 : ZMod 2628498527)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (18510553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (18510553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2628498527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_71
      · exact prime_twentyR_18510553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2628498527) ^ 1314249263 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2628498527) ^ 37021106 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2628498527) ^ 142 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_3586803617 : Nat.Prime 3586803617 := by
  apply lucas_primality 3586803617 (3 : ZMod 3586803617)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (17, 1), (599399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (17, 1), (599399, 1)] : List FactorBlock).map factorBlockValue).prod) = 3586803617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_twentyR_599399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3586803617) ^ 1793401808 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3586803617) ^ 326073056 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3586803617) ^ 210988448 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3586803617) ^ 5984 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_4070273261 : Nat.Prime 4070273261 := by
  apply lucas_primality 4070273261 (2 : ZMod 4070273261)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (97, 1), (2098079, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070273261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_97
      · exact prime_twentyR_2098079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4070273261) ^ 2035136630 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 814054652 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 41961580 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070273261) ^ 1940 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5368526563 : Nat.Prime 5368526563 := by
  apply lucas_primality 5368526563 (7 : ZMod 5368526563)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (2411737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (2411737, 1)] : List FactorBlock).map factorBlockValue).prod) = 5368526563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_twentyR_2411737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5368526563) ^ 2684263281 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 5368526563) ^ 1789508854 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 5368526563) ^ 766932366 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 5368526563) ^ 101292954 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 5368526563) ^ 2226 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_6008897029 : Nat.Prime 6008897029 := by
  apply lucas_primality 6008897029 (2 : ZMod 6008897029)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (16152949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (16152949, 1)] : List FactorBlock).map factorBlockValue).prod) = 6008897029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_twentyR_16152949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6008897029) ^ 3004448514 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6008897029) ^ 2002965676 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6008897029) ^ 193835388 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6008897029) ^ 372 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_6389032997 : Nat.Prime 6389032997 := by
  apply lucas_primality 6389032997 (2 : ZMod 6389032997)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1597258249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1597258249, 1)] : List FactorBlock).map factorBlockValue).prod) = 6389032997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1597258249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6389032997) ^ 3194516498 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6389032997) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_twentyR_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_8408707693 : Nat.Prime 8408707693 := by
  apply lucas_primality 8408707693 (15 : ZMod 8408707693)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 2), (827303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 2), (827303, 1)] : List FactorBlock).map factorBlockValue).prod) = 8408707693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyR_827303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 8408707693) ^ 4204353846 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 2802902564 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 1201243956 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 764427972 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 8408707693) ^ 10164 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_9278485297 : Nat.Prime 9278485297 := by
  apply lucas_primality 9278485297 (5 : ZMod 9278485297)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193301777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9278485297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_193301777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9278485297) ^ 4639242648 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 3092828432 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278485297) ^ 48 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10855569737 : Nat.Prime 10855569737 := by
  apply lucas_primality 10855569737 (5 : ZMod 10855569737)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (139, 1), (809, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (139, 1), (809, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 10855569737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_139
      · exact prime_twentyR_809
      · exact prime_twentyR_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10855569737) ^ 5427784868 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 986869976 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 78097624 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 13418504 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855569737) ^ 9895688 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10971529141 : Nat.Prime 10971529141 := by
  apply lucas_primality 10971529141 (2 : ZMod 10971529141)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (1278733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (1278733, 1)] : List FactorBlock).map factorBlockValue).prod) = 10971529141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentyR_1278733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10971529141) ^ 5485764570 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 3657176380 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 2194305828 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 997411740 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 843963780 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10971529141) ^ 8580 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_11673052829 : Nat.Prime 11673052829 := by
  apply lucas_primality 11673052829 (3 : ZMod 11673052829)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (126881009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (126881009, 1)] : List FactorBlock).map factorBlockValue).prod) = 11673052829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyR_126881009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11673052829) ^ 5836526414 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11673052829) ^ 507524036 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 11673052829) ^ 92 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15383, 1), (64153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842387189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_15383
      · exact prime_twentyR_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_13156468219 : Nat.Prime 13156468219 := by
  apply lucas_primality 13156468219 (2 : ZMod 13156468219)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (347, 1), (2106383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (347, 1), (2106383, 1)] : List FactorBlock).map factorBlockValue).prod) = 13156468219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_347
      · exact prime_twentyR_2106383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13156468219) ^ 6578234109 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13156468219) ^ 4385489406 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13156468219) ^ 37914894 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13156468219) ^ 6246 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_349
      · exact prime_twentyR_619
      · exact prime_twentyR_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_15993076399 : Nat.Prime 15993076399 := by
  apply lucas_primality 15993076399 (3 : ZMod 15993076399)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (205039441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (205039441, 1)] : List FactorBlock).map factorBlockValue).prod) = 15993076399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyR_205039441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15993076399) ^ 7996538199 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 15993076399) ^ 5331025466 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 15993076399) ^ 1230236646 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 15993076399) ^ 78 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_twentyR_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_17755350889 : Nat.Prime 17755350889 := by
  apply lucas_primality 17755350889 (14 : ZMod 17755350889)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) = 17755350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_twentyR_3539743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17755350889) ^ 8877675444 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5918450296 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 1614122808 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 934492152 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5016 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_24330664621 : Nat.Prime 24330664621 := by
  apply lucas_primality 24330664621 (2 : ZMod 24330664621)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) = 24330664621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_135170359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24330664621) ^ 12165332310 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 8110221540 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 4866132924 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 180 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 2), (21347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26687336297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_71
      · exact prime_twentyR_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyR_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_30384297329 : Nat.Prime 30384297329 := by
  apply lucas_primality 30384297329 (3 : ZMod 30384297329)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) = 30384297329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyR_1709
      · exact prime_twentyR_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30384297329) ^ 15192148664 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 4340613904 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2762208848 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 17778992 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30384297329) ^ 2105488 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_30569989673 : Nat.Prime 30569989673 := by
  apply lucas_primality 30569989673 (3 : ZMod 30569989673)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4783, 1), (798923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4783, 1), (798923, 1)] : List FactorBlock).map factorBlockValue).prod) = 30569989673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_4783
      · exact prime_twentyR_798923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30569989673) ^ 15284994836 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30569989673) ^ 6391384 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 30569989673) ^ 38264 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_51033940343 : Nat.Prime 51033940343 := by
  apply lucas_primality 51033940343 (10 : ZMod 51033940343)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (30126293, 1)] : List FactorBlock).map factorBlockValue).prod) = 51033940343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyR_30126293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 51033940343) ^ 25516970171 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 7290562906 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 4639449122 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 51033940343) ^ 1694 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_59236225667 : Nat.Prime 59236225667 := by
  apply lucas_primality 59236225667 (2 : ZMod 59236225667)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (3253, 1), (43151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (3253, 1), (43151, 1)] : List FactorBlock).map factorBlockValue).prod) = 59236225667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_211
      · exact prime_twentyR_3253
      · exact prime_twentyR_43151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59236225667) ^ 29618112833 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59236225667) ^ 280740406 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59236225667) ^ 18209722 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59236225667) ^ 1372766 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_61139979347 : Nat.Prime 61139979347 := by
  apply lucas_primality 61139979347 (2 : ZMod 61139979347)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30569989673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30569989673, 1)] : List FactorBlock).map factorBlockValue).prod) = 61139979347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_30569989673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 61139979347) ^ 30569989673 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 61139979347) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_63083964649 : Nat.Prime 63083964649 := by
  apply lucas_primality 63083964649 (7 : ZMod 63083964649)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2628498527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2628498527, 1)] : List FactorBlock).map factorBlockValue).prod) = 63083964649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_2628498527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 63083964649) ^ 31541982324 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63083964649) ^ 21027988216 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63083964649) ^ 24 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_66845788267 : Nat.Prime 66845788267 := by
  apply lucas_primality 66845788267 (3 : ZMod 66845788267)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (809, 1), (30671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (809, 1), (30671, 1)] : List FactorBlock).map factorBlockValue).prod) = 66845788267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_449
      · exact prime_twentyR_809
      · exact prime_twentyR_30671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66845788267) ^ 33422894133 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66845788267) ^ 22281929422 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66845788267) ^ 148877034 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66845788267) ^ 82627674 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 66845788267) ^ 2179446 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_71172712477 : Nat.Prime 71172712477 := by
  apply lucas_primality 71172712477 (2 : ZMod 71172712477)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (659006597, 1)] : List FactorBlock).map factorBlockValue).prod) = 71172712477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_659006597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71172712477) ^ 35586356238 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 23724237492 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71172712477) ^ 108 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_80248255349 : Nat.Prime 80248255349 := by
  apply lucas_primality 80248255349 (2 : ZMod 80248255349)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (739, 1), (27147583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (739, 1), (27147583, 1)] : List FactorBlock).map factorBlockValue).prod) = 80248255349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_739
      · exact prime_twentyR_27147583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 80248255349) ^ 40124127674 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 80248255349) ^ 108590332 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 80248255349) ^ 2956 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_82299631397 : Nat.Prime 82299631397 := by
  apply lucas_primality 82299631397 (2 : ZMod 82299631397)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod) = 82299631397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_29
      · exact prime_twentyR_41734093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82299631397) ^ 41149815698 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 4841154788 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 2837918324 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 82299631397) ^ 1972 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_90332674877 : Nat.Prime 90332674877 := by
  apply lucas_primality 90332674877 (2 : ZMod 90332674877)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (426097523, 1)] : List FactorBlock).map factorBlockValue).prod) = 90332674877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentyR_426097523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90332674877) ^ 45166337438 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 1704390092 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 90332674877) ^ 212 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_98043152197 : Nat.Prime 98043152197 := by
  apply lucas_primality 98043152197 (2 : ZMod 98043152197)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (10099, 1), (73547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (10099, 1), (73547, 1)] : List FactorBlock).map factorBlockValue).prod) = 98043152197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyR_10099
      · exact prime_twentyR_73547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98043152197) ^ 49021576098 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 32681050732 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 8913013836 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 9708204 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98043152197) ^ 1333068 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_102067880687 : Nat.Prime 102067880687 := by
  apply lucas_primality 102067880687 (5 : ZMod 102067880687)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51033940343, 1)] : List FactorBlock).map factorBlockValue).prod) = 102067880687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_51033940343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 102067880687) ^ 51033940343 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 102067880687) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_121827752369 : Nat.Prime 121827752369 := by
  apply lucas_primality 121827752369 (3 : ZMod 121827752369)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1087747789, 1)] : List FactorBlock).map factorBlockValue).prod) = 121827752369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_1087747789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 121827752369) ^ 60913876184 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 17403964624 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 121827752369) ^ 112 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_141780919669 : Nat.Prime 141780919669 := by
  apply lucas_primality 141780919669 (2 : ZMod 141780919669)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (110421277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (110421277, 1)] : List FactorBlock).map factorBlockValue).prod) = 141780919669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_107
      · exact prime_twentyR_110421277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 141780919669) ^ 70890459834 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 47260306556 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 1325055324 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 141780919669) ^ 1284 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_161869470179 : Nat.Prime 161869470179 := by
  apply lucas_primality 161869470179 (2 : ZMod 161869470179)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (59, 1), (271, 1), (9497, 1)] : List FactorBlock).map factorBlockValue).prod) = 161869470179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_t64_59
      · exact prime_twentyR_271
      · exact prime_twentyR_9497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161869470179) ^ 80934735089 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 12451497706 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 3948035858 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 2743550342 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 597304318 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 161869470179) ^ 17044274 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_219613389623 : Nat.Prime 219613389623 := by
  apply lucas_primality 219613389623 (5 : ZMod 219613389623)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) = 219613389623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_61
      · exact prime_twentyR_163646341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 219613389623) ^ 109806694811 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 19964853602 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 3600219502 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 1342 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_236131189291 : Nat.Prime 236131189291 := by
  apply lucas_primality 236131189291 (2 : ZMod 236131189291)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (34367, 1), (76343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (34367, 1), (76343, 1)] : List FactorBlock).map factorBlockValue).prod) = 236131189291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_34367
      · exact prime_twentyR_76343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 236131189291) ^ 118065594645 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 78710396430 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 47226237858 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 6870870 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 236131189291) ^ 3093030 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_237841108607 : Nat.Prime 237841108607 := by
  apply lucas_primality 237841108607 (5 : ZMod 237841108607)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) = 237841108607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_1093
      · exact prime_twentyR_3509741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237841108607) ^ 118920554303 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 7672293826 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 217603942 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 67766 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_247971379897 : Nat.Prime 247971379897 := by
  apply lucas_primality 247971379897 (5 : ZMod 247971379897)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (59, 1), (1009, 1), (57853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (59, 1), (1009, 1), (57853, 1)] : List FactorBlock).map factorBlockValue).prod) = 247971379897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_twentyR_1009
      · exact prime_twentyR_57853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 247971379897) ^ 123985689948 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 247971379897) ^ 82657126632 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 247971379897) ^ 4202904744 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 247971379897) ^ 245759544 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 247971379897) ^ 4286232 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_249951341833 : Nat.Prime 249951341833 := by
  apply lucas_primality 249951341833 (5 : ZMod 249951341833)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (73, 1), (3035453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (73, 1), (3035453, 1)] : List FactorBlock).map factorBlockValue).prod) = 249951341833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_t64_73
      · exact prime_twentyR_3035453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 249951341833) ^ 124975670916 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 83317113944 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 5318113656 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 3423990984 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 249951341833) ^ 82344 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_309443352821 : Nat.Prime 309443352821 := by
  apply lucas_primality 309443352821 (2 : ZMod 309443352821)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (37, 1), (59738099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (37, 1), (59738099, 1)] : List FactorBlock).map factorBlockValue).prod) = 309443352821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_twentyR_59738099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 309443352821) ^ 154721676410 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 61888670564 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 44206193260 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 8363333860 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 309443352821) ^ 5180 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_366921263173 : Nat.Prime 366921263173 := by
  apply lucas_primality 366921263173 (5 : ZMod 366921263173)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (105801979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (105801979, 1)] : List FactorBlock).map factorBlockValue).prod) = 366921263173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_105801979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 366921263173) ^ 183460631586 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 122307087724 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 21583603716 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 366921263173) ^ 3468 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_433811930261 : Nat.Prime 433811930261 := by
  apply lucas_primality 433811930261 (2 : ZMod 433811930261)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (263, 1), (4483, 1), (18397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (263, 1), (4483, 1), (18397, 1)] : List FactorBlock).map factorBlockValue).prod) = 433811930261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_263
      · exact prime_twentyR_4483
      · exact prime_twentyR_18397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 433811930261) ^ 216905965130 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433811930261) ^ 86762386052 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433811930261) ^ 1649475020 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433811930261) ^ 96768220 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433811930261) ^ 23580580 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_493797788383 : Nat.Prime 493797788383 := by
  apply lucas_primality 493797788383 (3 : ZMod 493797788383)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod) = 493797788383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_82299631397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 493797788383) ^ 246898894191 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 164599262794 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 493797788383) ^ 6 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_884357212127 : Nat.Prime 884357212127 := by
  apply lucas_primality 884357212127 (5 : ZMod 884357212127)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (76001, 1), (342239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (76001, 1), (342239, 1)] : List FactorBlock).map factorBlockValue).prod) = 884357212127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyR_76001
      · exact prime_twentyR_342239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 884357212127) ^ 442178606063 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 884357212127) ^ 52021012478 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 884357212127) ^ 11636126 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 884357212127) ^ 2584034 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1013900596351 : Nat.Prime 1013900596351 := by
  apply lucas_primality 1013900596351 (3 : ZMod 1013900596351)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (31, 1), (12826067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (31, 1), (12826067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013900596351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_31
      · exact prime_twentyR_12826067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1013900596351) ^ 506950298175 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 337966865450 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 202780119270 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 59641211550 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 32706470850 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013900596351) ^ 79050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1372447766351 : Nat.Prime 1372447766351 := by
  apply lucas_primality 1372447766351 (7 : ZMod 1372447766351)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (9473, 1), (170447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1372447766351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_twentyR_9473
      · exact prime_twentyR_170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1372447766351) ^ 686223883175 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 274489553270 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 80732221550 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 144879950 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1372447766351) ^ 8052050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_397
      · exact prime_twentyR_977
      · exact prime_twentyR_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1483112670203 : Nat.Prime 1483112670203 := by
  apply lucas_primality 1483112670203 (2 : ZMod 1483112670203)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483112670203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyR_30871
      · exact prime_twentyR_1044397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483112670203) ^ 741556335101 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 64483159574 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 48042262 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 1420066 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1529752406099 : Nat.Prime 1529752406099 := by
  apply lucas_primality 1529752406099 (2 : ZMod 1529752406099)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1529752406099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_t64_89
      · exact prime_t64_617
      · exact prime_twentyR_42337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1529752406099) ^ 764876203049 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 218536058014 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 32547923534 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 17188229282 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 2479339394 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 36132754 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_twentyR_9739
      · exact prime_twentyR_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2729747741957 : Nat.Prime 2729747741957 := by
  apply lucas_primality 2729747741957 (2 : ZMod 2729747741957)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (241, 1), (2053, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (241, 1), (2053, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729747741957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_149
      · exact prime_twentyR_241
      · exact prime_twentyR_2053
      · exact prime_twentyR_9257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2729747741957) ^ 1364873870978 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 18320454644 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 11326754116 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 1329638452 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729747741957) ^ 294884708 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_761
      · exact prime_twentyR_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_3687861576799 : Nat.Prime 3687861576799 := by
  apply lucas_primality 3687861576799 (3 : ZMod 3687861576799)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (44647, 1), (655559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (44647, 1), (655559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687861576799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyR_44647
      · exact prime_twentyR_655559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687861576799) ^ 1843930788399 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 1229287192266 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 526837368114 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 82600434 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687861576799) ^ 5625522 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_4937977883831 : Nat.Prime 4937977883831 := by
  apply lucas_primality 4937977883831 (11 : ZMod 4937977883831)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod) = 4937977883831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_493797788383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4937977883831) ^ 2468988941915 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 987595576766 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 4937977883831) ^ 10 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_381559
      · exact prime_twentyR_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5134675637989 : Nat.Prime 5134675637989 := by
  apply lucas_primality 5134675637989 (2 : ZMod 5134675637989)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (10971529141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (10971529141, 1)] : List FactorBlock).map factorBlockValue).prod) = 5134675637989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyR_10971529141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5134675637989) ^ 2567337818994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 1711558545996 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 394975049076 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134675637989) ^ 468 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5502598141231 : Nat.Prime 5502598141231 := by
  apply lucas_primality 5502598141231 (6 : ZMod 5502598141231)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61139979347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61139979347, 1)] : List FactorBlock).map factorBlockValue).prod) = 5502598141231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_61139979347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5502598141231) ^ 2751299070615 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 1834199380410 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 1100519628246 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5502598141231) ^ 90 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5686502827427 : Nat.Prime 5686502827427 := by
  apply lucas_primality 5686502827427 (2 : ZMod 5686502827427)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (98043152197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (98043152197, 1)] : List FactorBlock).map factorBlockValue).prod) = 5686502827427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_twentyR_98043152197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5686502827427) ^ 2843251413713 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5686502827427) ^ 196086304394 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5686502827427) ^ 58 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_8926899565049 : Nat.Prime 8926899565049 := by
  apply lucas_primality 8926899565049 (3 : ZMod 8926899565049)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (10567, 1), (1025231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (10567, 1), (1025231, 1)] : List FactorBlock).map factorBlockValue).prod) = 8926899565049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_103
      · exact prime_twentyR_10567
      · exact prime_twentyR_1025231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8926899565049) ^ 4463449782524 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8926899565049) ^ 86668927816 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8926899565049) ^ 844790344 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8926899565049) ^ 8707208 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_13327406448887 : Nat.Prime 13327406448887 := by
  apply lucas_primality 13327406448887 (5 : ZMod 13327406448887)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (141780919669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (141780919669, 1)] : List FactorBlock).map factorBlockValue).prod) = 13327406448887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_twentyR_141780919669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13327406448887) ^ 6663703224443 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 13327406448887) ^ 283561839338 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 13327406448887) ^ 94 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_14751446307197 : Nat.Prime 14751446307197 := by
  apply lucas_primality 14751446307197 (2 : ZMod 14751446307197)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3687861576799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3687861576799, 1)] : List FactorBlock).map factorBlockValue).prod) = 14751446307197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_3687861576799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14751446307197) ^ 7375723153598 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14751446307197) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_17754677904151 : Nat.Prime 17754677904151 := by
  apply lucas_primality 17754677904151 (11 : ZMod 17754677904151)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (11, 1), (3586803617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (11, 1), (3586803617, 1)] : List FactorBlock).map factorBlockValue).prod) = 17754677904151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentyR_3586803617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 17754677904151) ^ 8877338952075 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 17754677904151) ^ 5918225968050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 17754677904151) ^ 3550935580830 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 17754677904151) ^ 1614061627650 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (11 : ZMod 17754677904151) ^ 4950 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_17853799130099 : Nat.Prime 17853799130099 := by
  apply lucas_primality 17853799130099 (2 : ZMod 17853799130099)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8926899565049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8926899565049, 1)] : List FactorBlock).map factorBlockValue).prod) = 17853799130099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_8926899565049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 17853799130099) ^ 8926899565049 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 17853799130099) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyR_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_36209809875559 : Nat.Prime 36209809875559 := by
  apply lucas_primality 36209809875559 (3 : ZMod 36209809875559)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (47, 1), (11673052829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (47, 1), (11673052829, 1)] : List FactorBlock).map factorBlockValue).prod) = 36209809875559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_47
      · exact prime_twentyR_11673052829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36209809875559) ^ 18104904937779 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 12069936625186 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 3291800897778 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 770421486714 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36209809875559) ^ 3102 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_42038753447953 : Nat.Prime 42038753447953 := by
  apply lucas_primality 42038753447953 (7 : ZMod 42038753447953)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (47857, 1), (6100169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (47857, 1), (6100169, 1)] : List FactorBlock).map factorBlockValue).prod) = 42038753447953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_47857
      · exact prime_twentyR_6100169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42038753447953) ^ 21019376723976 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 14012917815984 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 878424336 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42038753447953) ^ 6891408 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_56191230356363 : Nat.Prime 56191230356363 := by
  apply lucas_primality 56191230356363 (2 : ZMod 56191230356363)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (73, 1), (653, 1), (20323781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (73, 1), (653, 1), (20323781, 1)] : List FactorBlock).map factorBlockValue).prod) = 56191230356363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_73
      · exact prime_twentyR_653
      · exact prime_twentyR_20323781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56191230356363) ^ 28095615178181 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 1937628632978 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 769742881594 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 86050888754 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 56191230356363) ^ 2764802 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_twentyR_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_77253599383361 : Nat.Prime 77253599383361 := by
  apply lucas_primality 77253599383361 (3 : ZMod 77253599383361)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11197, 1), (21560909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11197, 1), (21560909, 1)] : List FactorBlock).map factorBlockValue).prod) = 77253599383361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_11197
      · exact prime_twentyR_21560909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 77253599383361) ^ 38626799691680 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 77253599383361) ^ 15450719876672 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 77253599383361) ^ 6899490880 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 77253599383361) ^ 3583040 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_92149960118093 : Nat.Prime 92149960118093 := by
  apply lucas_primality 92149960118093 (2 : ZMod 92149960118093)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (281, 1), (1223641049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (281, 1), (1223641049, 1)] : List FactorBlock).map factorBlockValue).prod) = 92149960118093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_twentyR_281
      · exact prime_twentyR_1223641049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92149960118093) ^ 46074980059046 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 1375372539076 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 327935801132 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 92149960118093) ^ 75308 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_101351645184883 : Nat.Prime 101351645184883 := by
  apply lucas_primality 101351645184883 (2 : ZMod 101351645184883)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (1109, 1), (183514301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (1109, 1), (183514301, 1)] : List FactorBlock).map factorBlockValue).prod) = 101351645184883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_twentyR_1109
      · exact prime_twentyR_183514301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101351645184883) ^ 50675822592441 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 33783881728294 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 1221104158854 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 91390121898 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 101351645184883) ^ 552282 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_138616851326671 : Nat.Prime 138616851326671 := by
  apply lucas_primality 138616851326671 (3 : ZMod 138616851326671)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (501037, 1), (3073999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (501037, 1), (3073999, 1)] : List FactorBlock).map factorBlockValue).prod) = 138616851326671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_501037
      · exact prime_twentyR_3073999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138616851326671) ^ 69308425663335 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 46205617108890 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 27723370265334 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 276659910 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138616851326671) ^ 45093330 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_158796207522221 : Nat.Prime 158796207522221 := by
  apply lucas_primality 158796207522221 (2 : ZMod 158796207522221)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) = 158796207522221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_twentyR_14431
      · exact prime_twentyR_32364193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158796207522221) ^ 79398103761110 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 31759241504444 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 9340953383660 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 11003825620 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 4906540 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 2), (1163, 1), (1663, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 283615046165023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_twentyR_1163
      · exact prime_twentyR_1663
      · exact prime_twentyR_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_296123742126743 : Nat.Prime 296123742126743 := by
  apply lucas_primality 296123742126743 (5 : ZMod 296123742126743)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) = 296123742126743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_269
      · exact prime_twentyR_17755350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296123742126743) ^ 148061871063371 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 9552378778282 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 1100831755118 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 16678 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_386519565736481 : Nat.Prime 386519565736481 := by
  apply lucas_primality 386519565736481 (3 : ZMod 386519565736481)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) = 386519565736481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentyR_219613389623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 386519565736481) ^ 193259782868240 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 77303913147296 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 35138142339680 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 1760 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_405406580739533 : Nat.Prime 405406580739533 := by
  apply lucas_primality 405406580739533 (2 : ZMod 405406580739533)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101351645184883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101351645184883, 1)] : List FactorBlock).map factorBlockValue).prod) = 405406580739533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_101351645184883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 405406580739533) ^ 202703290369766 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 405406580739533) ^ 4 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_576001613200633 : Nat.Prime 576001613200633 := by
  apply lucas_primality 576001613200633 (5 : ZMod 576001613200633)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (121827752369, 1)] : List FactorBlock).map factorBlockValue).prod) = 576001613200633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_197
      · exact prime_twentyR_121827752369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 576001613200633) ^ 288000806600316 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 192000537733544 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 2923866056856 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 576001613200633) ^ 4728 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_800438006259989 : Nat.Prime 800438006259989 := by
  apply lucas_primality 800438006259989 (2 : ZMod 800438006259989)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14401, 1), (61553, 1), (225749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14401, 1), (61553, 1), (225749, 1)] : List FactorBlock).map factorBlockValue).prod) = 800438006259989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_14401
      · exact prime_twentyR_61553
      · exact prime_twentyR_225749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 800438006259989) ^ 400219003129994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 55582112788 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 13004045396 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 800438006259989) ^ 3545699012 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1045618291773007 : Nat.Prime 1045618291773007 := by
  apply lucas_primality 1045618291773007 (5 : ZMod 1045618291773007)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (47, 1), (71, 1), (152255011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045618291773007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_t64_71
      · exact prime_twentyR_152255011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1045618291773007) ^ 522809145886503 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 348539430591002 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 149374041681858 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 22247197697298 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 14727018193986 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1045618291773007) ^ 6867546 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1047858328388233 : Nat.Prime 1047858328388233 := by
  apply lucas_primality 1047858328388233 (5 : ZMod 1047858328388233)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (59, 1), (5351, 1), (46098109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (59, 1), (5351, 1), (46098109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047858328388233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_twentyR_5351
      · exact prime_twentyR_46098109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1047858328388233) ^ 523929164194116 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047858328388233) ^ 349286109462744 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047858328388233) ^ 17760310650648 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047858328388233) ^ 195824767032 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1047858328388233) ^ 22731048 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1388257266599051 : Nat.Prime 1388257266599051 := by
  apply lucas_primality 1388257266599051 (2 : ZMod 1388257266599051)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (352409, 1), (78786709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (352409, 1), (78786709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1388257266599051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_352409
      · exact prime_twentyR_78786709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1388257266599051) ^ 694128633299525 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 277651453319810 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 3939335450 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1388257266599051) ^ 17620450 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1447053552581521 : Nat.Prime 1447053552581521 := by
  apply lucas_primality 1447053552581521 (17 : ZMod 1447053552581521)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (29, 1), (15993076399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (29, 1), (15993076399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1447053552581521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_29
      · exact prime_twentyR_15993076399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1447053552581521) ^ 723526776290760 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1447053552581521) ^ 482351184193840 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1447053552581521) ^ 289410710516304 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1447053552581521) ^ 111311811737040 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1447053552581521) ^ 49898398364880 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1447053552581521) ^ 90480 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1472991480313183 : Nat.Prime 1472991480313183 := by
  apply lucas_primality 1472991480313183 (5 : ZMod 1472991480313183)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (156521, 1), (522823519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472991480313183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_156521
      · exact prime_twentyR_522823519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1472991480313183) ^ 736495740156591 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 490997160104394 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 9410823342 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1472991480313183) ^ 2817378 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2065202483007581 : Nat.Prime 2065202483007581 := by
  apply lucas_primality 2065202483007581 (3 : ZMod 2065202483007581)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (14751446307197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (14751446307197, 1)] : List FactorBlock).map factorBlockValue).prod) = 2065202483007581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyR_14751446307197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2065202483007581) ^ 1032601241503790 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 413040496601516 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 295028926143940 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2065202483007581) ^ 140 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2820880298726107 : Nat.Prime 2820880298726107 := by
  apply lucas_primality 2820880298726107 (3 : ZMod 2820880298726107)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820880298726107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_317
      · exact prime_twentyR_1483112670203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2820880298726107) ^ 1410440149363053 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 940293432908702 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 8898676021218 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 1902 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5523140549247743 : Nat.Prime 5523140549247743 := by
  apply lucas_primality 5523140549247743 (5 : ZMod 5523140549247743)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523140549247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_101
      · exact prime_twentyR_463
      · exact prime_twentyR_631
      · exact prime_twentyR_97387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5523140549247743) ^ 2761570274623871 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 178165824169282 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 54684559893542 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 11929029264034 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 8752996116082 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 56713324666 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10950386820164879 : Nat.Prime 10950386820164879 := by
  apply lucas_primality 10950386820164879 (17 : ZMod 10950386820164879)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3586771, 1), (1526496509, 1)] : List FactorBlock).map factorBlockValue).prod) = 10950386820164879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_3586771
      · exact prime_twentyR_1526496509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 10950386820164879) ^ 5475193410082439 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 3052993018 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (17 : ZMod 10950386820164879) ^ 7173542 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (11, 1), (67, 1), (97, 1), (247757789, 1)] : List FactorBlock).map factorBlockValue).prod) = 12398369604474701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_67
      · exact prime_t64_97
      · exact prime_twentyR_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_384973
      · exact prime_twentyR_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentyR_656951
      · exact prime_twentyR_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_26046963946467379 : Nat.Prime 26046963946467379 := by
  apply lucas_primality 26046963946467379 (2 : ZMod 26046963946467379)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1447053552581521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1447053552581521, 1)] : List FactorBlock).map factorBlockValue).prod) = 26046963946467379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_1447053552581521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26046963946467379) ^ 13023481973233689 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26046963946467379) ^ 8682321315489126 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 26046963946467379) ^ 18 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_28583317353999781 : Nat.Prime 28583317353999781 := by
  apply lucas_primality 28583317353999781 (2 : ZMod 28583317353999781)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) = 28583317353999781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyR_158796207522221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28583317353999781) ^ 14291658676999890 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 9527772451333260 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 5716663470799956 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 180 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_33531643827487633 : Nat.Prime 33531643827487633 := by
  apply lucas_primality 33531643827487633 (15 : ZMod 33531643827487633)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (509, 1), (1372447766351, 1)] : List FactorBlock).map factorBlockValue).prod) = 33531643827487633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_509
      · exact prime_twentyR_1372447766351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 33531643827487633) ^ 16765821913743816 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 11177214609162544 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 65877492784848 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (15 : ZMod 33531643827487633) ^ 24432 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_36146519348744033 : Nat.Prime 36146519348744033 := by
  apply lucas_primality 36146519348744033 (3 : ZMod 36146519348744033)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (887, 1), (11177, 1), (113937749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (887, 1), (11177, 1), (113937749, 1)] : List FactorBlock).map factorBlockValue).prod) = 36146519348744033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_887
      · exact prime_twentyR_11177
      · exact prime_twentyR_113937749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36146519348744033) ^ 18073259674372016 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36146519348744033) ^ 40751431058336 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36146519348744033) ^ 3234009067616 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 36146519348744033) ^ 317247968 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_42312414672901069 : Nat.Prime 42312414672901069 := by
  apply lucas_primality 42312414672901069 (2 : ZMod 42312414672901069)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (137, 1), (2963, 1), (57689, 1), (150571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (137, 1), (2963, 1), (57689, 1), (150571, 1)] : List FactorBlock).map factorBlockValue).prod) = 42312414672901069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_137
      · exact prime_t64_2963
      · exact prime_twentyR_57689
      · exact prime_twentyR_150571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42312414672901069) ^ 21156207336450534 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42312414672901069) ^ 14104138224300356 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42312414672901069) ^ 308849742137964 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42312414672901069) ^ 14280261448836 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42312414672901069) ^ 733457239212 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42312414672901069) ^ 281013041508 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_53513668657618357 : Nat.Prime 53513668657618357 := by
  apply lucas_primality 53513668657618357 (2 : ZMod 53513668657618357)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (405406580739533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (405406580739533, 1)] : List FactorBlock).map factorBlockValue).prod) = 53513668657618357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyR_405406580739533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53513668657618357) ^ 26756834328809178 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 17837889552539452 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 4864878968874396 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 53513668657618357) ^ 132 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_63981475582964197 : Nat.Prime 63981475582964197 := by
  apply lucas_primality 63981475582964197 (2 : ZMod 63981475582964197)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6029, 1), (884357212127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6029, 1), (884357212127, 1)] : List FactorBlock).map factorBlockValue).prod) = 63981475582964197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_6029
      · exact prime_twentyR_884357212127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63981475582964197) ^ 31990737791482098 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 63981475582964197) ^ 21327158527654732 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 63981475582964197) ^ 10612286545524 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 63981475582964197) ^ 72348 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_81991102561369319 : Nat.Prime 81991102561369319 := by
  apply lucas_primality 81991102561369319 (13 : ZMod 81991102561369319)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2309, 1), (17754677904151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2309, 1), (17754677904151, 1)] : List FactorBlock).map factorBlockValue).prod) = 81991102561369319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_2309
      · exact prime_twentyR_17754677904151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 81991102561369319) ^ 40995551280684659 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 81991102561369319) ^ 35509355808302 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 81991102561369319) ^ 4618 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_134692530919461259 : Nat.Prime 134692530919461259 := by
  apply lucas_primality 134692530919461259 (3 : ZMod 134692530919461259)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1433, 1), (210961, 1), (74258111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1433, 1), (210961, 1), (74258111, 1)] : List FactorBlock).map factorBlockValue).prod) = 134692530919461259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_1433
      · exact prime_twentyR_210961
      · exact prime_twentyR_74258111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 134692530919461259) ^ 67346265459730629 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 134692530919461259) ^ 44897510306487086 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 134692530919461259) ^ 93993392128026 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 134692530919461259) ^ 638471238378 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 134692530919461259) ^ 1813842678 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_190813341386997503 : Nat.Prime 190813341386997503 := by
  apply lucas_primality 190813341386997503 (5 : ZMod 190813341386997503)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod) = 190813341386997503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_twentyR_4937977883831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190813341386997503) ^ 95406670693498751 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 1372757851705018 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 190813341386997503) ^ 38642 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13421, 1), (99611, 1), (23622671, 1)] : List FactorBlock).map factorBlockValue).prod) = 252645265925168009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_13421
      · exact prime_twentyR_99611
      · exact prime_twentyR_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_430766070161620937 : Nat.Prime 430766070161620937 := by
  apply lucas_primality 430766070161620937 (3 : ZMod 430766070161620937)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (41, 1), (77253599383361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (41, 1), (77253599383361, 1)] : List FactorBlock).map factorBlockValue).prod) = 430766070161620937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_twentyR_77253599383361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 430766070161620937) ^ 215383035080810468 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 430766070161620937) ^ 25339180597742408 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 430766070161620937) ^ 10506489516137096 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 430766070161620937) ^ 5576 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_518500159195792793 : Nat.Prime 518500159195792793 := by
  apply lucas_primality 518500159195792793 (3 : ZMod 518500159195792793)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131, 1), (5477, 1), (90332674877, 1)] : List FactorBlock).map factorBlockValue).prod) = 518500159195792793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_131
      · exact prime_twentyR_5477
      · exact prime_twentyR_90332674877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518500159195792793) ^ 259250079597896396 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 3958016482410632 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 94668643271096 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 518500159195792793) ^ 5739896 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_853224526086773713 : Nat.Prime 853224526086773713 := by
  apply lucas_primality 853224526086773713 (5 : ZMod 853224526086773713)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (1045618291773007, 1)] : List FactorBlock).map factorBlockValue).prod) = 853224526086773713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyR_1045618291773007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 853224526086773713) ^ 426612263043386856 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 284408175362257904 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 50189678005104336 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 853224526086773713) ^ 816 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1249558476287426663 : Nat.Prime 1249558476287426663 := by
  apply lucas_primality 1249558476287426663 (5 : ZMod 1249558476287426663)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (874459, 1), (102067880687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1249558476287426663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyR_874459
      · exact prime_twentyR_102067880687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1249558476287426663) ^ 624779238143713331 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 178508353755346666 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 1428950329618 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1249558476287426663) ^ 12242426 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2499116952574853327 : Nat.Prime 2499116952574853327 := by
  apply lucas_primality 2499116952574853327 (5 : ZMod 2499116952574853327)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1249558476287426663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2499116952574853327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1249558476287426663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2499116952574853327) ^ 1249558476287426663 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2499116952574853327) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_3030158014634483503 : Nat.Prime 3030158014634483503 := by
  apply lucas_primality 3030158014634483503 (3 : ZMod 3030158014634483503)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod) = 3030158014634483503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyR_6514591
      · exact prime_twentyR_143826233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3030158014634483503) ^ 1515079007317241751 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 1010052671544827834 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 432879716376354786 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 275468910421316682 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 465134037522 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3030158014634483503) ^ 21068187294 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_3775351412811012257 : Nat.Prime 3775351412811012257 := by
  apply lucas_primality 3775351412811012257 (3 : ZMod 3775351412811012257)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (52023863, 1), (2267800291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3775351412811012257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_52023863
      · exact prime_twentyR_2267800291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3775351412811012257) ^ 1887675706405506128 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 72569609312 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3775351412811012257) ^ 1664763616 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10613706022307444107 : Nat.Prime 10613706022307444107 := by
  apply lucas_primality 10613706022307444107 (3 : ZMod 10613706022307444107)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (431, 1), (9461, 1), (433811930261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (431, 1), (9461, 1), (433811930261, 1)] : List FactorBlock).map factorBlockValue).prod) = 10613706022307444107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_431
      · exact prime_twentyR_9461
      · exact prime_twentyR_433811930261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10613706022307444107) ^ 5306853011153722053 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10613706022307444107) ^ 3537902007435814702 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10613706022307444107) ^ 24625768033195926 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10613706022307444107) ^ 1121837651654946 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10613706022307444107) ^ 24466146 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10822794222674765767 : Nat.Prime 10822794222674765767 := by
  apply lucas_primality 10822794222674765767 (3 : ZMod 10822794222674765767)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26984483, 1), (66845788267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26984483, 1), (66845788267, 1)] : List FactorBlock).map factorBlockValue).prod) = 10822794222674765767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_26984483
      · exact prime_twentyR_66845788267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10822794222674765767) ^ 5411397111337382883 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10822794222674765767) ^ 3607598074224921922 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10822794222674765767) ^ 401074729602 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10822794222674765767) ^ 161906898 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_45023731903529596433 : Nat.Prime 45023731903529596433 := by
  apply lucas_primality 45023731903529596433 (3 : ZMod 45023731903529596433)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7411, 1), (93287, 1), (4070273261, 1)] : List FactorBlock).map factorBlockValue).prod) = 45023731903529596433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_7411
      · exact prime_twentyR_93287
      · exact prime_twentyR_4070273261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45023731903529596433) ^ 22511865951764798216 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 6075257307182512 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 482636722196336 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45023731903529596433) ^ 11061599312 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_65689486876996052887 : Nat.Prime 65689486876996052887 := by
  apply lucas_primality 65689486876996052887 (3 : ZMod 65689486876996052887)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59659, 1), (2017843, 1), (10105057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59659, 1), (2017843, 1), (10105057, 1)] : List FactorBlock).map factorBlockValue).prod) = 65689486876996052887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_59659
      · exact prime_twentyR_2017843
      · exact prime_twentyR_10105057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65689486876996052887) ^ 32844743438498026443 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 21896495625665350962 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 1101082600730754 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 32554310160402 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 65689486876996052887) ^ 6500654758998 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_94525107910918353337 : Nat.Prime 94525107910918353337 := by
  apply lucas_primality 94525107910918353337 (10 : ZMod 94525107910918353337)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (103, 1), (13025219, 1), (62461991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (103, 1), (13025219, 1), (62461991, 1)] : List FactorBlock).map factorBlockValue).prod) = 94525107910918353337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_t64_103
      · exact prime_twentyR_13025219
      · exact prime_twentyR_62461991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 94525107910918353337) ^ 47262553955459176668 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 94525107910918353337) ^ 31508369303639451112 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 94525107910918353337) ^ 2011172508742943688 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 94525107910918353337) ^ 917719494280760712 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 94525107910918353337) ^ 7257083962344 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (10 : ZMod 94525107910918353337) ^ 1513322044296 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_101627574192727747903 : Nat.Prime 101627574192727747903 := by
  apply lucas_primality 101627574192727747903 (3 : ZMod 101627574192727747903)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3833, 1), (1472991480313183, 1)] : List FactorBlock).map factorBlockValue).prod) = 101627574192727747903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_3833
      · exact prime_twentyR_1472991480313183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101627574192727747903) ^ 50813787096363873951 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 33875858064242582634 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 26513846645637294 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 101627574192727747903) ^ 68994 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_138564817290563326591 : Nat.Prime 138564817290563326591 := by
  apply lucas_primality 138564817290563326591 (3 : ZMod 138564817290563326591)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (383, 1), (1429, 1), (366921263173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (383, 1), (1429, 1), (366921263173, 1)] : List FactorBlock).map factorBlockValue).prod) = 138564817290563326591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_383
      · exact prime_twentyR_1429
      · exact prime_twentyR_366921263173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138564817290563326591) ^ 69282408645281663295 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 46188272430187775530 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 27712963458112665318 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 6024557273502753330 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 361788034701209730 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 96966282218728710 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 138564817290563326591) ^ 377641830 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1286602568459335170893 : Nat.Prime 1286602568459335170893 := by
  apply lucas_primality 1286602568459335170893 (2 : ZMod 1286602568459335170893)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (102452173, 1), (59236225667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (102452173, 1), (59236225667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1286602568459335170893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentyR_102452173
      · exact prime_twentyR_59236225667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1286602568459335170893) ^ 643301284229667585446 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1286602568459335170893) ^ 24275520159610097564 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1286602568459335170893) ^ 12558079841404 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1286602568459335170893) ^ 21719860676 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_2020562502386822800799 : Nat.Prime 2020562502386822800799 := by
  apply lucas_primality 2020562502386822800799 (7 : ZMod 2020562502386822800799)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1423, 1), (2801, 1), (36209809875559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1423, 1), (2801, 1), (36209809875559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020562502386822800799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_1423
      · exact prime_twentyR_2801
      · exact prime_twentyR_36209809875559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2020562502386822800799) ^ 1010281251193411400399 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 288651786055260400114 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 1419931484460170626 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 721371832340886398 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2020562502386822800799) ^ 55801522 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_4041125004773645601599 : Nat.Prime 4041125004773645601599 := by
  apply lucas_primality 4041125004773645601599 (13 : ZMod 4041125004773645601599)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2020562502386822800799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2020562502386822800799, 1)] : List FactorBlock).map factorBlockValue).prod) = 4041125004773645601599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_2020562502386822800799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 4041125004773645601599) ^ 2020562502386822800799 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (13 : ZMod 4041125004773645601599) ^ 2 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_6891984566505300835487 : Nat.Prime 6891984566505300835487 := by
  apply lucas_primality 6891984566505300835487 (5 : ZMod 6891984566505300835487)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6891984566505300835487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_11637001
      · exact prime_twentyR_296123742126743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6891984566505300835487) ^ 3445992283252650417743 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 592247484253486 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 23274002 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_10084938184863487564601 : Nat.Prime 10084938184863487564601 := by
  apply lucas_primality 10084938184863487564601 (3 : ZMod 10084938184863487564601)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (97, 1), (50101, 1), (119557, 1), (86786087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (97, 1), (50101, 1), (119557, 1), (86786087, 1)] : List FactorBlock).map factorBlockValue).prod) = 10084938184863487564601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_97
      · exact prime_twentyR_50101
      · exact prime_twentyR_119557
      · exact prime_twentyR_86786087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10084938184863487564601) ^ 5042469092431743782300 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 2016987636972697512920 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 103968434895499871800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 201292153547104600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 84352553048867800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10084938184863487564601) ^ 116204549985800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_19647584683708272101017 : Nat.Prime 19647584683708272101017 := by
  apply lucas_primality 19647584683708272101017 (5 : ZMod 19647584683708272101017)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (103, 1), (596369, 1), (13327406448887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (103, 1), (596369, 1), (13327406448887, 1)] : List FactorBlock).map factorBlockValue).prod) = 19647584683708272101017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_103
      · exact prime_twentyR_596369
      · exact prime_twentyR_13327406448887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19647584683708272101017) ^ 9823792341854136050508 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 6549194894569424033672 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 190753249356390991272 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 32945348741648664 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 19647584683708272101017) ^ 1474224168 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_126545132708901892665503 : Nat.Prime 126545132708901892665503 := by
  apply lucas_primality 126545132708901892665503 (5 : ZMod 126545132708901892665503)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1750447, 1), (36146519348744033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1750447, 1), (36146519348744033, 1)] : List FactorBlock).map factorBlockValue).prod) = 126545132708901892665503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_1750447
      · exact prime_twentyR_36146519348744033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 126545132708901892665503) ^ 63272566354450946332751 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 126545132708901892665503) ^ 72293038697488066 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 126545132708901892665503) ^ 3500894 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_463261646167912959194123 : Nat.Prime 463261646167912959194123 := by
  apply lucas_primality 463261646167912959194123 (2 : ZMod 463261646167912959194123)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (242989, 1), (18337103, 1), (115779767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (242989, 1), (18337103, 1), (115779767, 1)] : List FactorBlock).map factorBlockValue).prod) = 463261646167912959194123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyR_449
      · exact prime_twentyR_242989
      · exact prime_twentyR_18337103
      · exact prime_twentyR_115779767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 463261646167912959194123) ^ 231630823083956479597061 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 1031763131777088995978 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 1906512830489910898 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 25263622403599574 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 463261646167912959194123) ^ 4001231460138566 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyR_3061
      · exact prime_twentyR_61379
      · exact prime_twentyR_382747
      · exact prime_twentyR_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyR_1321
      · exact prime_twentyR_1255074433
      · exact prime_twentyR_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_4141765227195033342131237 : Nat.Prime 4141765227195033342131237 := by
  apply lucas_primality 4141765227195033342131237 (2 : ZMod 4141765227195033342131237)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (30083567, 1), (800438006259989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (30083567, 1), (800438006259989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4141765227195033342131237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_twentyR_30083567
      · exact prime_twentyR_800438006259989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4141765227195033342131237) ^ 2070882613597516671065618 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 96320121562675194003052 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 137675337076718108 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4141765227195033342131237) ^ 5174373524 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_5251018805697633877465519 : Nat.Prime 5251018805697633877465519 := by
  apply lucas_primality 5251018805697633877465519 (6 : ZMod 5251018805697633877465519)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (101, 1), (5387, 1), (19853, 1), (615493, 1), (10125847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (101, 1), (5387, 1), (19853, 1), (615493, 1), (10125847, 1)] : List FactorBlock).map factorBlockValue).prod) = 5251018805697633877465519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_101
      · exact prime_twentyR_5387
      · exact prime_twentyR_19853
      · exact prime_twentyR_615493
      · exact prime_twentyR_10125847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5251018805697633877465519) ^ 2625509402848816938732759 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 1750339601899211292488506 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 403924523515202605958886 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 51990285204927068093718 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 974757528438395002314 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 264494978375944888806 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 8531402965911283926 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (6 : ZMod 5251018805697633877465519) ^ 518575760200369794 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_246305600854754639064867001 : Nat.Prime 246305600854754639064867001 := by
  apply lucas_primality 246305600854754639064867001 (103 : ZMod 246305600854754639064867001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 246305600854754639064867001 - 1 by
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
    · change (103 : ZMod 246305600854754639064867001) ^ 123152800427377319532433500 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 82101866951584879688289000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 49261120170950927812973400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 35186514407822091294981000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 22391418259523149005897000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 18946584681134972235759000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 14488564756162037592051000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 12963452676566033634993000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 10708939167598027785429000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 8493296581198435829823000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 7945341963056601260157000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6656908131209584839591000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 6007453679384259489387000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5728037229180340443369000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 5240544699037332746061000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4647275487825559227639000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4174671200928044729913000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (103 : ZMod 246305600854754639064867001) ^ 4037796735323846542047000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_288357776610444455490576001 : Nat.Prime 288357776610444455490576001 := by
  apply lucas_primality 288357776610444455490576001 (41 : ZMod 288357776610444455490576001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 288357776610444455490576001 - 1 by
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
    · change (41 : ZMod 288357776610444455490576001) ^ 144178888305222227745288000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 96119258870148151830192000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 57671555322088891098115200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 41193968087206350784368000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 26214343328222223226416000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 22181367431572650422352000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 16962222153555556205328000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 15176725084760234499504000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 12537294635236715456112000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 9943371607256705361744000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 9301863761627240499696000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 7793453421903904202448000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 6705994804894057104432000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 6135271842775413946608000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 5440712766234801046992000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 4887419942549906025264000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (41 : ZMod 288357776610444455490576001) ^ 4727176665744991073616000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_375322820350102307146464001 : Nat.Prime 375322820350102307146464001 := by
  apply lucas_primality 375322820350102307146464001 (71 : ZMod 375322820350102307146464001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 375322820350102307146464001 - 1 by
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
    · change (71 : ZMod 375322820350102307146464001) ^ 187661410175051153573232000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 125107606783367435715488000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 75064564070020461429292800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 53617545764300329592352000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 34120256395463846104224000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 28870986180777100549728000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 22077812961770723949792000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 19753832650005384586656000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 16318383493482709006368000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 12942166218969045074016000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 12107187753229106682144000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 10143860009462224517472000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 9154215130490300174304000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 8728437682560518770848000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 7985591922342602279712000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 7081562648115137870688000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 6361403734747496731296000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 375322820350102307146464001) ^ 6152833120493480445024000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_407678235897524919831504001 : Nat.Prime 407678235897524919831504001 := by
  apply lucas_primality 407678235897524919831504001 (67 : ZMod 407678235897524919831504001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 407678235897524919831504001 - 1 by
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
    · change (67 : ZMod 407678235897524919831504001) ^ 203839117948762459915752000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 135892745299174973277168000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 81535647179504983966300800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 58239747985360702833072000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 37061657808865901802864000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 31359864299809609217808000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 23981072699854407048912000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 21456749257764469464816000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 17725140691196735644848000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 13150910835404029671984000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 11018330699933105941392000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9943371607256705361744000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 9480889206919184182128000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 8674005019096274890032000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 7692042186745753204368000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6909800608432625759856000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 407678235897524919831504001) ^ 6683249768811883931664000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_437876623741786025004208001 : Nat.Prime 437876623741786025004208001 := by
  apply lucas_primality 437876623741786025004208001 (12 : ZMod 437876623741786025004208001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 437876623741786025004208001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
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
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 437876623741786025004208001) ^ 218938311870893012502104000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 87575324748357205000841600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 62553803391683717857744000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 39806965794707820454928000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 33682817210906617308016000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 25757448455399177941424000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 23046138091672948684432000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 19038114075729827174096000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 15099193922130552586352000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 14125052378767291129168000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 11834503344372595270384000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10679917652238683536688000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 10183177296320605232656000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 9316523909399702659664000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 8261823089467660849136000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7421637690538746186512000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (12 : ZMod 437876623741786025004208001) ^ 7178305307242393852528000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_482557911878702966331168001 : Nat.Prime 482557911878702966331168001 := by
  apply lucas_primality 482557911878702966331168001 (7 : ZMod 482557911878702966331168001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 482557911878702966331168001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
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
    · change (7 : ZMod 482557911878702966331168001) ^ 241278955939351483165584000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 160852637292900988777056000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 96511582375740593266233600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 43868901079882087848288000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 37119839375284843563936000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 28385759522276645078304000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 25397784835721208754272000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 20980778777334911579616000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 16639927995817343666592000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 15566384254151708591328000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 13042105726451431522464000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 11769705167773243081248000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 11222277020434952705376000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 10267189614440488645344000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 9104866261862320119456000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 8178947658961067225952000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (7 : ZMod 482557911878702966331168001) ^ 7910785440634474857888000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_503092291107583943621856001 : Nat.Prime 503092291107583943621856001 := by
  apply lucas_primality 503092291107583943621856001 (73 : ZMod 503092291107583943621856001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 503092291107583943621856001 - 1 by
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
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 503092291107583943621856001) ^ 251546145553791971810928000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 167697430369194647873952000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 100618458221516788724371200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 71870327301083420517408000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 45735662827962176692896000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 38699407008275687970912000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 29593664182799055507168000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 26478541637241260190624000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 21873577874242780157472000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 17348010038192549780064000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 16228783584115611084576000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 13597088948853620097888000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 12270543685550827893216000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 11699820723432184735392000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 9492307379388376294752000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 8526987984874304129184000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (73 : ZMod 503092291107583943621856001) ^ 8247414608321048256096000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
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
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_606290709796319111544288001 : Nat.Prime 606290709796319111544288001 := by
  apply lucas_primality 606290709796319111544288001 (65 : ZMod 606290709796319111544288001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 606290709796319111544288001 - 1 by
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
    · change (65 : ZMod 606290709796319111544288001) ^ 303145354898159555772144000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 202096903265439703848096000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 121258141959263822308857600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 86612958542331301649184000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 55117337254210828322208000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 35664159399783477149664000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 31910037357701005870752000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 26360465643318222241056000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 20906576199873072811872000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 19557764832139326178848000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 16386235399900516528224000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 14787578287715100281568000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 14099783948751607245216000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 12899802336091895990304000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 11439447354647530406496000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 10276113725361340873632000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (65 : ZMod 606290709796319111544288001) ^ 9939191963874083795808000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_815356471795049839663008001 : Nat.Prime 815356471795049839663008001 := by
  apply lucas_primality 815356471795049839663008001 (71 : ZMod 815356471795049839663008001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 815356471795049839663008001 - 1 by
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
    · change (71 : ZMod 815356471795049839663008001) ^ 407678235897524919831504000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 271785490598349946554336000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 163071294359009967932601600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 116479495970721405666144000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 74123315617731803605728000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 62719728599619218435616000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 47962145399708814097824000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 42913498515528938929632000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 35450281382393471289696000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 26301821670808059343968000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 22036661399866211882784000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 19886743214513410723488000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 18961778413838368364256000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 17348010038192549780064000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 15384084373491506408736000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 13819601216865251519712000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (71 : ZMod 815356471795049839663008001) ^ 13366499537623767863328000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_909436064694478667316432001 : Nat.Prime 909436064694478667316432001 := by
  apply lucas_primality 909436064694478667316432001 (26 : ZMod 909436064694478667316432001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478667316432001 - 1 by
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
    · change (26 : ZMod 909436064694478667316432001) ^ 454718032347239333658216000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 303145354898159555772144000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 181887212938895733463286400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 129919437813496952473776000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 82676005881316242483312000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 53496239099675215724496000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 47865056036551508806128000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 39540698464977333361584000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 31359864299809609217808000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 29336647248208989268272000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 24579353099850774792336000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 22181367431572650422352000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 21149675923127410867824000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 19349703504137843985456000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 17159171031971295609744000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 15414170588042011310448000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 14908787945811125693712000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1074788076457111152283056001 : Nat.Prime 1074788076457111152283056001 := by
  apply lucas_primality 1074788076457111152283056001 (67 : ZMod 1074788076457111152283056001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074788076457111152283056001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
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
    · change (67 : ZMod 1074788076457111152283056001) ^ 537394038228555576141528000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 358262692152370384094352000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 214957615291422230456611200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 153541153779587307469008000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 82676005881316242483312000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 63222828026888891310768000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 56567793497742692225424000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 46729916367700484881872000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 37061657808865901802864000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 34670583111519714589776000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 29048326390732733845488000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 26214343328222223226416000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 24995071545514212843792000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 22867831413981088346448000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 20279020310511531175152000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 18216747058595104275984000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 17619476663231330365296000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
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
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
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
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem prime_twentyR_23645337682056445350227232067 : Nat.Prime 23645337682056445350227232067 := by
  apply lucas_primality 23645337682056445350227232067 (3 : ZMod 23645337682056445350227232067)
  · rw [← twentyRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (467, 1), (1479571, 1), (518500159195792793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (467, 1), (1479571, 1), (518500159195792793, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_467
      · exact prime_twentyR_1479571
      · exact prime_twentyR_518500159195792793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056445350227232067) ^ 11822668841028222675113616033 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445350227232067) ^ 7881779227352148450075744022 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445350227232067) ^ 2149576152914222304566112006 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445350227232067) ^ 50632414736737570343098998 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445350227232067) ^ 15981211906732725465846 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445350227232067) ^ 45603337362 ≠ 1
      rw [← twentyRFastPow_eq_pow]
      decide

private theorem phi_twentyR_23645337682056445350227232000 : Nat.totient 23645337682056445350227232000 = 3111427369187212787712000000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232001 : Nat.totient 23645337682056445350227232001 = 23543826289993479239786926080 := by
  rw [← show ((([(233, 1), (806041, 1), (503705849, 1), (249951341833, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_233, prime_twentyR_806041, prime_twentyR_503705849, prime_twentyR_249951341833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232002 : Nat.totient 23645337682056445350227232002 = 11802992225090850041226588048 := by
  rw [← show ((([(2, 1), (859, 1), (1997, 1), (6891984566505300835487, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_859, prime_twentyR_1997, prime_twentyR_6891984566505300835487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232003 : Nat.totient 23645337682056445350227232003 = 15733417806114018982710235200 := by
  rw [← show ((([(3, 1), (523, 1), (10855569737, 1), (1388257266599051, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyR_523, prime_twentyR_10855569737, prime_twentyR_1388257266599051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232004 : Nat.totient 23645337682056445350227232004 = 11822586549148761105448221024 := by
  rw [← show ((([(2, 2), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyR_143669, prime_twentyR_13852339783, prime_twentyR_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232005 : Nat.totient 23645337682056445350227232005 = 18867038531782032696231936000 := by
  rw [← show ((([(5, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_twentyR_401, prime_twentyR_11069, prime_twentyR_53269, prime_twentyR_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232006 : Nat.totient 23645337682056445350227232006 = 7881757901737286031539712000 := by
  rw [← show ((([(2, 1), (3, 1), (374681, 1), (27212041, 1), (386519565736481, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_374681, prime_twentyR_27212041, prime_twentyR_386519565736481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232007 : Nat.totient 23645337682056445350227232007 = 20267432238308654920777827840 := by
  rw [← show ((([(7, 1), (569284721, 1), (928715773, 1), (6389032997, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_twentyR_569284721, prime_twentyR_928715773, prime_twentyR_6389032997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232008 : Nat.totient 23645337682056445350227232008 = 11767234303164905839260297216 := by
  rw [← show ((([(2, 3), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_223, prime_twentyR_5113, prime_twentyR_101287, prime_twentyR_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232009 : Nat.totient 23645337682056445350227232009 = 15741444341253626736493920480 := by
  rw [← show ((([(3, 2), (733, 1), (25867, 1), (138564817290563326591, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyR_733, prime_twentyR_25867, prime_twentyR_138564817290563326591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232010 : Nat.totient 23645337682056445350227232010 = 9458090075438874484030430208 := by
  rw [← show ((([(2, 1), (5, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232011 : Nat.totient 23645337682056445350227232011 = 21391548028433671764639744000 := by
  rw [← show ((([(11, 1), (457, 1), (541, 1), (1409, 1), (9221, 1), (1363189, 1), (490901413, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_twentyR_457, prime_twentyR_541, prime_t64_1409, prime_twentyR_9221, prime_twentyR_1363189, prime_twentyR_490901413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232012 : Nat.totient 23645337682056445350227232012 = 7773808969736782162807334400 := by
  rw [← show ((([(2, 2), (3, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_73, prime_twentyR_13737811, prime_twentyR_68784581, prime_twentyR_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232013 : Nat.totient 23645337682056445350227232013 = 21826382798805270041685288960 := by
  rw [← show ((([(13, 2), (263761, 1), (8408707693, 1), (63083964649, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_twentyR_263761, prime_twentyR_8408707693, prime_twentyR_63083964649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232014 : Nat.totient 23645337682056445350227232014 = 10118658610368043988843969280 := by
  rw [← show ((([(2, 1), (7, 1), (673, 1), (889647091, 1), (2820880298726107, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_673, prime_twentyR_889647091, prime_twentyR_2820880298726107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232015 : Nat.totient 23645337682056445350227232015 = 12610846763763437520121190400 := by
  rw [← show ((([(3, 1), (5, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyR_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232016 : Nat.totient 23645337682056445350227232016 = 11822668841028222675113616000 := by
  rw [← show ((([(2, 4), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyR_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232017 : Nat.totient 23645337682056445350227232017 = 22219690299709146537467750400 := by
  rw [← show ((([(17, 1), (1193, 1), (1783, 1), (6547, 1), (98507, 1), (1013900596351, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_twentyR_1193, prime_t64_1783, prime_twentyR_6547, prime_twentyR_98507, prime_twentyR_1013900596351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232018 : Nat.totient 23645337682056445350227232018 = 7881779227319008179733605912 := by
  rw [← show ((([(2, 1), (3, 2), (237841108607, 1), (5523140549247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_237841108607, prime_twentyR_5523140549247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232019 : Nat.totient 23645337682056445350227232019 = 22400664696218778578489520000 := by
  rw [← show ((([(19, 1), (123401, 1), (10084938184863487564601, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_twentyR_123401, prime_twentyR_10084938184863487564601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232020 : Nat.totient 23645337682056445350227232020 = 9364438622826365116007809536 := by
  rw [← show ((([(2, 2), (5, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232021 : Nat.totient 23645337682056445350227232021 = 13511272301655791381217192960 := by
  rw [← show ((([(3, 1), (7, 1), (39607, 1), (1719547, 1), (82478129, 1), (200447861, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentyR_39607, prime_twentyR_1719547, prime_twentyR_82478129, prime_twentyR_200447861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232022 : Nat.totient 23645337682056445350227232022 = 10747880764571111522830560000 := by
  rw [← show ((([(2, 1), (11, 1), (1074788076457111152283056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyR_1074788076457111152283056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232023 : Nat.totient 23645337682056445350227232023 = 22273840472311341637723043616 := by
  rw [← show ((([(23, 1), (67, 1), (3797, 1), (4041125004773645601599, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_67, prime_twentyR_3797, prime_twentyR_4041125004773645601599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232024 : Nat.totient 23645337682056445350227232024 = 7841024215338702655066963968 := by
  rw [← show ((([(2, 3), (3, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_283, prime_twentyR_613, prime_twentyR_85303, prime_twentyR_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232025 : Nat.totient 23645337682056445350227232025 = 18720983448928097847799520000 := by
  rw [← show ((([(5, 2), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_107, prime_twentyR_1013, prime_twentyR_144417341, prime_twentyR_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232026 : Nat.totient 23645337682056445350227232026 = 10913232776333744007797184000 := by
  rw [← show ((([(2, 1), (13, 1), (909436064694478667316432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_twentyR_909436064694478667316432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232027 : Nat.totient 23645337682056445350227232027 = 15576955815502448333459716608 := by
  rw [← show ((([(3, 4), (89, 1), (1723, 1), (35573, 1), (53513668657618357, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_89, prime_twentyR_1723, prime_twentyR_35573, prime_twentyR_53513668657618357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232028 : Nat.totient 23645337682056445350227232028 = 10043852580825757730349465600 := by
  rw [← show ((([(2, 2), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_113, prime_twentyR_54421, prime_twentyR_97654321, prime_twentyR_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232029 : Nat.totient 23645337682056445350227232029 = 22829981210261395510564224000 := by
  rw [← show ((([(29, 1), (815356471795049839663008001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_twentyR_815356471795049839663008001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232030 : Nat.totient 23645337682056445350227232030 = 6286198917043595648577024000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232031 : Nat.totient 23645337682056445350227232031 = 22882584853598688045768123000 := by
  rw [← show ((([(31, 1), (5502598141231, 1), (138616851326671, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_twentyR_5502598141231, prime_twentyR_138616851326671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232032 : Nat.totient 23645337682056445350227232032 = 11680218790863874308291942400 := by
  rw [← show ((([(2, 5), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_83, prime_twentyR_1433741, prime_twentyR_106163831, prime_twentyR_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232033 : Nat.totient 23645337682056445350227232033 = 14247672381550914696931451840 := by
  rw [← show ((([(3, 1), (11, 1), (173, 1), (4141765227195033342131237, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentyR_173, prime_twentyR_4141765227195033342131237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232034 : Nat.totient 23645337682056445350227232034 = 11127217732275111403740537600 := by
  rw [← show ((([(2, 1), (17, 1), (24330664621, 1), (28583317353999781, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyR_24330664621, prime_twentyR_28583317353999781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232035 : Nat.totient 23645337682056445350227232035 = 16199029605601766108774387808 := by
  rw [← show ((([(5, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_twentyR_1087, prime_twentyR_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232036 : Nat.totient 23645337682056445350227232036 = 7867709727577369037199576576 := by
  rw [← show ((([(2, 2), (3, 2), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_569, prime_twentyR_37039, prime_twentyR_1544987, prime_twentyR_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232037 : Nat.totient 23645337682056445350227232037 = 23006274501385966776277521600 := by
  rw [← show ((([(37, 1), (309443352821, 1), (2065202483007581, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_twentyR_309443352821, prime_twentyR_2065202483007581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232038 : Nat.totient 23645337682056445350227232038 = 11200418434272921159565566720 := by
  rw [← show ((([(2, 1), (19, 1), (2428859, 1), (167470561, 1), (1529752406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentyR_2428859, prime_twentyR_167470561, prime_twentyR_1529752406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232039 : Nat.totient 23645337682056445350227232039 = 14550977035111658677062912000 := by
  rw [← show ((([(3, 1), (13, 1), (606290709796319111544288001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_twentyR_606290709796319111544288001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232040 : Nat.totient 23645337682056445350227232040 = 9458135065086595926115297600 := by
  rw [← show ((([(2, 3), (5, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232041 : Nat.totient 23645337682056445350227232041 = 22797485460200382284250885120 := by
  rw [← show ((([(41, 1), (149, 1), (197, 1), (19647584683708272101017, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_149, prime_t64_197, prime_twentyR_19647584683708272101017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232042 : Nat.totient 23645337682056445350227232042 = 6755810736312438095034832944 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (225273263, 1), (2499116952574853327, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentyR_225273263, prime_twentyR_2499116952574853327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232043 : Nat.totient 23645337682056445350227232043 = 23075989118916080323377605064 := by
  rw [← show ((([(43, 1), (1187, 1), (463261646167912959194123, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_twentyR_1187, prime_twentyR_463261646167912959194123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232044 : Nat.totient 23645337682056445350227232044 = 10596502161856110116733916800 := by
  rw [← show ((([(2, 2), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_71, prime_twentyR_26687336297, prime_twentyR_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232045 : Nat.totient 23645337682056445350227232045 = 12610846763763437520121190400 := by
  rw [← show ((([(3, 2), (5, 1), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyR_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232046 : Nat.totient 23645337682056445350227232046 = 11294998259025162011501587680 := by
  rw [← show ((([(2, 1), (23, 1), (829, 1), (56624411, 1), (10950386820164879, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentyR_829, prime_twentyR_56624411, prime_twentyR_10950386820164879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232047 : Nat.totient 23645337682056445350227232047 = 23142245390948861406605376000 := by
  rw [← show ((([(47, 1), (503092291107583943621856001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_twentyR_503092291107583943621856001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232048 : Nat.totient 23645337682056445350227232048 = 7809459068838695435749075968 := by
  rw [← show ((([(2, 4), (3, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_109, prime_twentyR_762563, prime_twentyR_500452427, prime_twentyR_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232049 : Nat.totient 23645337682056445350227232049 = 20267432298905524585909056000 := by
  rw [← show ((([(7, 2), (482557911878702966331168001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_twentyR_482557911878702966331168001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232050 : Nat.totient 23645337682056445350227232050 = 9416376836876748091987690560 := by
  rw [← show ((([(2, 1), (5, 2), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232051 : Nat.totient 23645337682056445350227232051 = 14828331148365386708995276800 := by
  rw [← show ((([(3, 1), (17, 1), (1867, 1), (1217921, 1), (37980161, 1), (5368526563, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_twentyR_1867, prime_twentyR_1217921, prime_twentyR_37980161, prime_twentyR_5368526563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232052 : Nat.totient 23645337682056445350227232052 = 10888675595149121812154112000 := by
  rw [← show ((([(2, 2), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_twentyR_599, prime_twentyR_1811, prime_twentyR_33809, prime_twentyR_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232053 : Nat.totient 23645337682056445350227232053 = 23013408677929389828338368320 := by
  rw [← show ((([(53, 1), (131, 1), (2647, 1), (1286602568459335170893, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_twentyR_131, prime_twentyR_2647, prime_twentyR_1286602568459335170893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232054 : Nat.totient 23645337682056445350227232054 = 7881779227352148450075744000 := by
  rw [← show ((([(2, 1), (3, 3), (437876623741786025004208001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_437876623741786025004208001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232055 : Nat.totient 23645337682056445350227232055 = 17193523517369590080698426880 := by
  rw [← show ((([(5, 1), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_twentyR_5573, prime_twentyR_3198253273, prime_twentyR_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232056 : Nat.totient 23645337682056445350227232056 = 10133716143389275870640042496 := by
  rw [← show ((([(2, 3), (7, 1), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyR_1671268889, prime_twentyR_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232057 : Nat.totient 23645337682056445350227232057 = 14744860806398955927923174544 := by
  rw [← show ((([(3, 1), (19, 1), (79, 1), (5251018805697633877465519, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_t64_79, prime_twentyR_5251018805697633877465519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232058 : Nat.totient 23645337682056445350227232058 = 11414990605130697755282112000 := by
  rw [← show ((([(2, 1), (29, 1), (407678235897524919831504001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_twentyR_407678235897524919831504001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232059 : Nat.totient 23645337682056445350227232059 = 23237229629070236746380801256 := by
  rw [← show ((([(59, 1), (3167, 1), (126545132708901892665503, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_twentyR_3167, prime_twentyR_126545132708901892665503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232060 : Nat.totient 23645337682056445350227232060 = 6305423381881718760060595200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232061 : Nat.totient 23645337682056445350227232061 = 23245661762043031044491193600 := by
  rw [← show ((([(61, 1), (2477, 1), (8747, 1), (222943571, 1), (80248255349, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_twentyR_2477, prime_twentyR_8747, prime_twentyR_222943571, prime_twentyR_80248255349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232062 : Nat.totient 23645337682056445350227232062 = 11378061674065835775260208000 := by
  rw [← show ((([(2, 1), (31, 1), (181, 1), (609781, 1), (21346979, 1), (161869470179, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_twentyR_181, prime_twentyR_609781, prime_twentyR_21346979, prime_twentyR_161869470179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232063 : Nat.totient 23645337682056445350227232063 = 13511621532603683057272704000 := by
  rw [← show ((([(3, 2), (7, 1), (375322820350102307146464001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentyR_375322820350102307146464001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232064 : Nat.totient 23645337682056445350227232064 = 11822668813725037826480400384 := by
  rw [← show ((([(2, 6), (433014277, 1), (853224526086773713, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyR_433014277, prime_twentyR_853224526086773713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232065 : Nat.totient 23645337682056445350227232065 = 17391606018061743438720600000 := by
  rw [← show ((([(5, 1), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_251, prime_twentyR_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232066 : Nat.totient 23645337682056445350227232066 = 7149905854645094396537980800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (467, 1), (1479571, 1), (518500159195792793, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_467, prime_twentyR_1479571, prime_twentyR_518500159195792793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232067 : Nat.totient 23645337682056445350227232067 = 23645337682056445350227232066 := by
  rw [← show ((([(23645337682056445350227232067, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_23645337682056445350227232067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232068 : Nat.totient 23645337682056445350227232068 = 11127214480650070703297745024 := by
  rw [← show ((([(2, 2), (17, 1), (3421567, 1), (101627574192727747903, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyR_3421567, prime_twentyR_101627574192727747903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232069 : Nat.totient 23645337682056445350227232069 = 15078186346831956129354865776 := by
  rw [← show ((([(3, 1), (23, 1), (13156468219, 1), (26046963946467379, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_twentyR_13156468219, prime_twentyR_26046963946467379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232070 : Nat.totient 23645337682056445350227232070 = 8106889790731887118593367008 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232071 : Nat.totient 23645337682056445350227232071 = 23484602354687484130411200000 := by
  rw [← show ((([(151, 1), (6067, 1), (86353, 1), (153704071, 1), (1944606701, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_151, prime_twentyR_6067, prime_twentyR_86353, prime_twentyR_153704071, prime_twentyR_1944606701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232072 : Nat.totient 23645337682056445350227232072 = 7881778146782582765190371328 := by
  rw [← show ((([(2, 3), (3, 2), (7294097, 1), (45023731903529596433, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_7294097, prime_twentyR_45023731903529596433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232073 : Nat.totient 23645337682056445350227232073 = 23645159099613698117606338128 := by
  rw [← show ((([(141613, 1), (2036459, 1), (81991102561369319, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_141613, prime_twentyR_2036459, prime_twentyR_81991102561369319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232074 : Nat.totient 23645337682056445350227232074 = 11503137250727935004418631632 := by
  rw [← show ((([(2, 1), (37, 1), (5686502827427, 1), (56191230356363, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_twentyR_5686502827427, prime_twentyR_56191230356363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232075 : Nat.totient 23645337682056445350227232075 = 12610112765899390918480233600 := by
  rw [← show ((([(3, 1), (5, 2), (22397, 1), (73771, 1), (190813341386997503, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyR_22397, prime_twentyR_73771, prime_twentyR_190813341386997503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232076 : Nat.totient 23645337682056445350227232076 = 11200423111345913548818926592 := by
  rw [← show ((([(2, 2), (19, 1), (9278485297, 1), (33531643827487633, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentyR_9278485297, prime_twentyR_33531643827487633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232077 : Nat.totient 23645337682056445350227232077 = 18422883880317555389524540800 := by
  rw [← show ((([(7, 1), (11, 1), (10303, 1), (69191, 1), (430766070161620937, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_twentyR_10303, prime_twentyR_69191, prime_twentyR_430766070161620937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232078 : Nat.totient 23645337682056445350227232078 = 7237488988703119677715630080 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (193, 1), (23911, 1), (65689486876996052887, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_t64_193, prime_twentyR_23911, prime_twentyR_65689486876996052887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232079 : Nat.totient 23645337682056445350227232079 = 23637768072684337050943726080 := by
  rw [← show ((([(3593, 1), (25579, 1), (396631, 1), (4988569, 1), (130029563, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_3593, prime_twentyR_25579, prime_twentyR_396631, prime_twentyR_4988569, prime_twentyR_130029563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232080 : Nat.totient 23645337682056445350227232080 = 9458134620944793194601529344 := by
  rw [← show ((([(2, 4), (5, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232081 : Nat.totient 23645337682056445350227232081 = 15588841242728030001964948800 := by
  rw [← show ((([(3, 3), (157, 1), (211, 1), (196271, 1), (134692530919461259, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_157, prime_twentyR_211, prime_twentyR_196271, prime_twentyR_134692530919461259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232082 : Nat.totient 23645337682056445350227232082 = 11534311064417778219623040000 := by
  rw [← show ((([(2, 1), (41, 1), (288357776610444455490576001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_twentyR_288357776610444455490576001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232083 : Nat.totient 23645337682056445350227232083 = 23645330999018513199366588648 := by
  rw [← show ((([(3572203, 1), (370747939, 1), (17853799130099, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_3572203, prime_twentyR_370747939, prime_twentyR_17853799130099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232084 : Nat.totient 23645337682056445350227232084 = 6627867901468094239580160000 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (97, 1), (139, 1), (659, 1), (55001, 1), (576001613200633, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_97, prime_t64_139, prime_twentyR_659, prime_twentyR_55001, prime_twentyR_576001613200633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232085 : Nat.totient 23645337682056445350227232085 = 17548139520365768405381283840 := by
  rw [← show ((([(5, 1), (17, 1), (73, 1), (1609, 1), (29021, 1), (2685877, 1), (30384297329, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_t64_73, prime_twentyR_1609, prime_twentyR_29021, prime_twentyR_2685877, prime_twentyR_30384297329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232086 : Nat.totient 23645337682056445350227232086 = 11546985670968966383020746240 := by
  rw [← show ((([(2, 1), (43, 1), (15661, 1), (417616597, 1), (42038753447953, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_twentyR_15661, prime_twentyR_417616597, prime_twentyR_42038753447953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232087 : Nat.totient 23645337682056445350227232087 = 15201074133715917175399507200 := by
  rw [← show ((([(3, 1), (29, 1), (1223, 1), (2351, 1), (94525107910918353337, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_twentyR_1223, prime_twentyR_2351, prime_twentyR_94525107910918353337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232088 : Nat.totient 23645337682056445350227232088 = 10740352260811796824223769600 := by
  rw [← show ((([(2, 3), (11, 1), (1471, 1), (48383, 1), (3775351412811012257, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyR_1471, prime_twentyR_48383, prime_twentyR_3775351412811012257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232089 : Nat.totient 23645337682056445350227232089 = 23645337671442739325691976356 := by
  rw [← show ((([(2227811627, 1), (10613706022307444107, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_2227811627, prime_twentyR_10613706022307444107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232090 : Nat.totient 23645337682056445350227232090 = 6192819318588176905531084800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_67, prime_t64_491, prime_t64_1061, prime_t64_9492089, prime_lucas_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232091 : Nat.totient 23645337682056445350227232091 = 18708399045068097502640438784 := by
  rw [← show ((([(7, 1), (13, 1), (247971379897, 1), (1047858328388233, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_twentyR_247971379897, prime_twentyR_1047858328388233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232092 : Nat.totient 23645337682056445350227232092 = 11308639383650464384465962432 := by
  rw [← show ((([(2, 2), (23, 1), (56297287, 1), (64144099, 1), (71172712477, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentyR_56297287, prime_twentyR_64144099, prime_twentyR_71172712477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232093 : Nat.totient 23645337682056445350227232093 = 15255056566529929178593554240 := by
  rw [← show ((([(3, 1), (31, 1), (6008897029, 1), (42312414672901069, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_twentyR_6008897029, prime_twentyR_42312414672901069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232094 : Nat.totient 23645337682056445350227232094 = 11571122695470066236741125792 := by
  rw [← show ((([(2, 1), (47, 1), (2729747741957, 1), (92149960118093, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_twentyR_2729747741957, prime_twentyR_92149960118093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232095 : Nat.totient 23645337682056445350227232095 = 17881870619076969275621351424 := by
  rw [← show ((([(5, 1), (19, 1), (463, 1), (177409, 1), (3030158014634483503, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_twentyR_463, prime_twentyR_177409, prime_twentyR_3030158014634483503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232096 : Nat.totient 23645337682056445350227232096 = 7881779227352148450075744000 := by
  rw [← show ((([(2, 5), (3, 1), (246305600854754639064867001, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyR_246305600854754639064867001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232097 : Nat.totient 23645337682056445350227232097 = 23645337671233651125367694340 := by
  rw [← show ((([(2184771991, 1), (10822794222674765767, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyR_2184771991, prime_twentyR_10822794222674765767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232098 : Nat.totient 23645337682056445350227232098 = 10082792952677180259896692320 := by
  rw [← show ((([(2, 1), (7, 2), (199, 1), (236131189291, 1), (5134675637989, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyR_199, prime_twentyR_236131189291, prime_twentyR_5134675637989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyR_23645337682056445350227232099 : Nat.totient 23645337682056445350227232099 = 14188621087492151591120832000 := by
  rw [← show ((([(3, 2), (11, 1), (101, 1), (36960233, 1), (63981475582964197, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445350227232099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_t64_101, prime_twentyR_36960233, prime_twentyR_63981475582964197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyR : certifiedKill 1 23645337682056445350227231999 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyR_23645337682056445350227232000, phi_twentyR_23645337682056445350227232001, phi_twentyR_23645337682056445350227232002,
    phi_twentyR_23645337682056445350227232003, phi_twentyR_23645337682056445350227232004, phi_twentyR_23645337682056445350227232005,
    phi_twentyR_23645337682056445350227232006, phi_twentyR_23645337682056445350227232007, phi_twentyR_23645337682056445350227232008,
    phi_twentyR_23645337682056445350227232009, phi_twentyR_23645337682056445350227232010, phi_twentyR_23645337682056445350227232011,
    phi_twentyR_23645337682056445350227232012, phi_twentyR_23645337682056445350227232013, phi_twentyR_23645337682056445350227232014,
    phi_twentyR_23645337682056445350227232015, phi_twentyR_23645337682056445350227232016, phi_twentyR_23645337682056445350227232017,
    phi_twentyR_23645337682056445350227232018, phi_twentyR_23645337682056445350227232019, phi_twentyR_23645337682056445350227232020,
    phi_twentyR_23645337682056445350227232021, phi_twentyR_23645337682056445350227232022, phi_twentyR_23645337682056445350227232023,
    phi_twentyR_23645337682056445350227232024, phi_twentyR_23645337682056445350227232025, phi_twentyR_23645337682056445350227232026,
    phi_twentyR_23645337682056445350227232027, phi_twentyR_23645337682056445350227232028, phi_twentyR_23645337682056445350227232029,
    phi_twentyR_23645337682056445350227232030, phi_twentyR_23645337682056445350227232031, phi_twentyR_23645337682056445350227232032,
    phi_twentyR_23645337682056445350227232033, phi_twentyR_23645337682056445350227232034, phi_twentyR_23645337682056445350227232035,
    phi_twentyR_23645337682056445350227232036, phi_twentyR_23645337682056445350227232037, phi_twentyR_23645337682056445350227232038,
    phi_twentyR_23645337682056445350227232039, phi_twentyR_23645337682056445350227232040, phi_twentyR_23645337682056445350227232041,
    phi_twentyR_23645337682056445350227232042, phi_twentyR_23645337682056445350227232043, phi_twentyR_23645337682056445350227232044,
    phi_twentyR_23645337682056445350227232045, phi_twentyR_23645337682056445350227232046, phi_twentyR_23645337682056445350227232047,
    phi_twentyR_23645337682056445350227232048, phi_twentyR_23645337682056445350227232049, phi_twentyR_23645337682056445350227232050,
    phi_twentyR_23645337682056445350227232051, phi_twentyR_23645337682056445350227232052, phi_twentyR_23645337682056445350227232053,
    phi_twentyR_23645337682056445350227232054, phi_twentyR_23645337682056445350227232055, phi_twentyR_23645337682056445350227232056,
    phi_twentyR_23645337682056445350227232057, phi_twentyR_23645337682056445350227232058, phi_twentyR_23645337682056445350227232059,
    phi_twentyR_23645337682056445350227232060, phi_twentyR_23645337682056445350227232061, phi_twentyR_23645337682056445350227232062,
    phi_twentyR_23645337682056445350227232063, phi_twentyR_23645337682056445350227232064, phi_twentyR_23645337682056445350227232065,
    phi_twentyR_23645337682056445350227232066, phi_twentyR_23645337682056445350227232067, phi_twentyR_23645337682056445350227232068,
    phi_twentyR_23645337682056445350227232069, phi_twentyR_23645337682056445350227232070, phi_twentyR_23645337682056445350227232071,
    phi_twentyR_23645337682056445350227232072, phi_twentyR_23645337682056445350227232073, phi_twentyR_23645337682056445350227232074,
    phi_twentyR_23645337682056445350227232075, phi_twentyR_23645337682056445350227232076, phi_twentyR_23645337682056445350227232077,
    phi_twentyR_23645337682056445350227232078, phi_twentyR_23645337682056445350227232079, phi_twentyR_23645337682056445350227232080,
    phi_twentyR_23645337682056445350227232081, phi_twentyR_23645337682056445350227232082, phi_twentyR_23645337682056445350227232083,
    phi_twentyR_23645337682056445350227232084, phi_twentyR_23645337682056445350227232085, phi_twentyR_23645337682056445350227232086,
    phi_twentyR_23645337682056445350227232087, phi_twentyR_23645337682056445350227232088, phi_twentyR_23645337682056445350227232089,
    phi_twentyR_23645337682056445350227232090, phi_twentyR_23645337682056445350227232091, phi_twentyR_23645337682056445350227232092,
    phi_twentyR_23645337682056445350227232093, phi_twentyR_23645337682056445350227232094, phi_twentyR_23645337682056445350227232095,
    phi_twentyR_23645337682056445350227232096, phi_twentyR_23645337682056445350227232097, phi_twentyR_23645337682056445350227232098,
    phi_twentyR_23645337682056445350227232099]

end TotientTailPeriodKiller
end Erdos249257
