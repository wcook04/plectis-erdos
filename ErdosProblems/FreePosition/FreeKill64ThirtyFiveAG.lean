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
  prime_t64_191
  prime_t64_193
  prime_t64_223
  prime_t64_227
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_283
  prime_t64_307
  prime_t64_317
  prime_t64_349
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_433
  prime_t64_439
  prime_t64_479
  prime_t64_491
  prime_t64_521
  prime_t64_563
  prime_t64_607
  prime_t64_617
  prime_t64_647
  prime_t64_761
  prime_t64_991
  prime_t64_1093
  prime_t64_1153
  prime_t64_2251
  prime_t64_2909
  prime_t64_3511
  prime_t64_5009
  prime_t64_8093
  from Erdos249257.DiagonalPincerCertificatesT64

private def thirtyFiveAGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtyFiveAGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtyFiveAGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtyFiveAGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtyFiveAGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtyFiveAGFastPow a n * thirtyFiveAGFastPow a n * a
        else thirtyFiveAGFastPow a n * thirtyFiveAGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtyFiveAG_127 : Nat.Prime 127 := by norm_num

private theorem prime_thirtyFiveAG_131 : Nat.Prime 131 := by norm_num

private theorem prime_thirtyFiveAG_151 : Nat.Prime 151 := by norm_num

private theorem prime_thirtyFiveAG_181 : Nat.Prime 181 := by norm_num

private theorem prime_thirtyFiveAG_199 : Nat.Prime 199 := by norm_num

private theorem prime_thirtyFiveAG_211 : Nat.Prime 211 := by norm_num

private theorem prime_thirtyFiveAG_241 : Nat.Prime 241 := by norm_num

private theorem prime_thirtyFiveAG_257 : Nat.Prime 257 := by norm_num

private theorem prime_thirtyFiveAG_271 : Nat.Prime 271 := by norm_num

private theorem prime_thirtyFiveAG_281 : Nat.Prime 281 := by norm_num

private theorem prime_thirtyFiveAG_293 : Nat.Prime 293 := by norm_num

private theorem prime_thirtyFiveAG_313 : Nat.Prime 313 := by norm_num

private theorem prime_thirtyFiveAG_331 : Nat.Prime 331 := by norm_num

private theorem prime_thirtyFiveAG_347 : Nat.Prime 347 := by norm_num

private theorem prime_thirtyFiveAG_353 : Nat.Prime 353 := by norm_num

private theorem prime_thirtyFiveAG_359 : Nat.Prime 359 := by norm_num

private theorem prime_thirtyFiveAG_373 : Nat.Prime 373 := by norm_num

private theorem prime_thirtyFiveAG_389 : Nat.Prime 389 := by norm_num

private theorem prime_thirtyFiveAG_397 : Nat.Prime 397 := by norm_num

private theorem prime_thirtyFiveAG_443 : Nat.Prime 443 := by norm_num

private theorem prime_thirtyFiveAG_449 : Nat.Prime 449 := by norm_num

private theorem prime_thirtyFiveAG_457 : Nat.Prime 457 := by norm_num

private theorem prime_thirtyFiveAG_487 : Nat.Prime 487 := by norm_num

private theorem prime_thirtyFiveAG_503 : Nat.Prime 503 := by norm_num

private theorem prime_thirtyFiveAG_541 : Nat.Prime 541 := by norm_num

private theorem prime_thirtyFiveAG_557 : Nat.Prime 557 := by norm_num

private theorem prime_thirtyFiveAG_569 : Nat.Prime 569 := by norm_num

private theorem prime_thirtyFiveAG_599 : Nat.Prime 599 := by norm_num

private theorem prime_thirtyFiveAG_601 : Nat.Prime 601 := by norm_num

private theorem prime_thirtyFiveAG_613 : Nat.Prime 613 := by norm_num

private theorem prime_thirtyFiveAG_619 : Nat.Prime 619 := by norm_num

private theorem prime_thirtyFiveAG_677 : Nat.Prime 677 := by norm_num

private theorem prime_thirtyFiveAG_733 : Nat.Prime 733 := by norm_num

private theorem prime_thirtyFiveAG_823 : Nat.Prime 823 := by norm_num

private theorem prime_thirtyFiveAG_827 : Nat.Prime 827 := by norm_num

private theorem prime_thirtyFiveAG_829 : Nat.Prime 829 := by norm_num

private theorem prime_thirtyFiveAG_863 : Nat.Prime 863 := by norm_num

private theorem prime_thirtyFiveAG_881 : Nat.Prime 881 := by norm_num

private theorem prime_thirtyFiveAG_907 : Nat.Prime 907 := by norm_num

private theorem prime_thirtyFiveAG_967 : Nat.Prime 967 := by norm_num

private theorem prime_thirtyFiveAG_971 : Nat.Prime 971 := by norm_num

private theorem prime_thirtyFiveAG_977 : Nat.Prime 977 := by norm_num

private theorem prime_thirtyFiveAG_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_thirtyFiveAG_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_thirtyFiveAG_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_thirtyFiveAG_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_thirtyFiveAG_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_thirtyFiveAG_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_thirtyFiveAG_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_thirtyFiveAG_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_thirtyFiveAG_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_thirtyFiveAG_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_thirtyFiveAG_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_thirtyFiveAG_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_thirtyFiveAG_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_thirtyFiveAG_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_thirtyFiveAG_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_thirtyFiveAG_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_thirtyFiveAG_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_thirtyFiveAG_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_thirtyFiveAG_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_thirtyFiveAG_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_thirtyFiveAG_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_thirtyFiveAG_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_thirtyFiveAG_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_thirtyFiveAG_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_thirtyFiveAG_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_thirtyFiveAG_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_thirtyFiveAG_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_thirtyFiveAG_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_thirtyFiveAG_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_thirtyFiveAG_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_thirtyFiveAG_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_thirtyFiveAG_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_thirtyFiveAG_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_thirtyFiveAG_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_thirtyFiveAG_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_thirtyFiveAG_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_thirtyFiveAG_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_thirtyFiveAG_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_thirtyFiveAG_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_thirtyFiveAG_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_thirtyFiveAG_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_thirtyFiveAG_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_thirtyFiveAG_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_thirtyFiveAG_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_thirtyFiveAG_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_thirtyFiveAG_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_thirtyFiveAG_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_thirtyFiveAG_4831 : Nat.Prime 4831 := by norm_num

private theorem prime_thirtyFiveAG_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_thirtyFiveAG_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_thirtyFiveAG_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_thirtyFiveAG_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_thirtyFiveAG_5639 : Nat.Prime 5639 := by norm_num

private theorem prime_thirtyFiveAG_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_thirtyFiveAG_5749 : Nat.Prime 5749 := by norm_num

private theorem prime_thirtyFiveAG_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_thirtyFiveAG_5801 : Nat.Prime 5801 := by norm_num

private theorem prime_thirtyFiveAG_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_thirtyFiveAG_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_thirtyFiveAG_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_thirtyFiveAG_6037 : Nat.Prime 6037 := by norm_num

private theorem prime_thirtyFiveAG_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_thirtyFiveAG_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_thirtyFiveAG_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_thirtyFiveAG_6577 : Nat.Prime 6577 := by norm_num

private theorem prime_thirtyFiveAG_7237 : Nat.Prime 7237 := by norm_num

private theorem prime_thirtyFiveAG_7309 : Nat.Prime 7309 := by norm_num

private theorem prime_thirtyFiveAG_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_thirtyFiveAG_7507 : Nat.Prime 7507 := by norm_num

private theorem prime_thirtyFiveAG_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_thirtyFiveAG_7841 : Nat.Prime 7841 := by norm_num

private theorem prime_thirtyFiveAG_8053 : Nat.Prime 8053 := by norm_num

private theorem prime_thirtyFiveAG_8291 : Nat.Prime 8291 := by norm_num

private theorem prime_thirtyFiveAG_8389 : Nat.Prime 8389 := by norm_num

private theorem prime_thirtyFiveAG_8609 : Nat.Prime 8609 := by norm_num

private theorem prime_thirtyFiveAG_8681 : Nat.Prime 8681 := by norm_num

private theorem prime_thirtyFiveAG_8699 : Nat.Prime 8699 := by norm_num

private theorem prime_thirtyFiveAG_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_thirtyFiveAG_8863 : Nat.Prime 8863 := by norm_num

private theorem prime_thirtyFiveAG_9397 : Nat.Prime 9397 := by norm_num

private theorem prime_thirtyFiveAG_9431 : Nat.Prime 9431 := by norm_num

private theorem prime_thirtyFiveAG_9439 : Nat.Prime 9439 := by norm_num

private theorem prime_thirtyFiveAG_9511 : Nat.Prime 9511 := by norm_num

private theorem prime_thirtyFiveAG_9629 : Nat.Prime 9629 := by norm_num

private theorem prime_thirtyFiveAG_10223 : Nat.Prime 10223 := by norm_num

private theorem prime_thirtyFiveAG_10313 : Nat.Prime 10313 := by norm_num

private theorem prime_thirtyFiveAG_10391 : Nat.Prime 10391 := by norm_num

private theorem prime_thirtyFiveAG_10667 : Nat.Prime 10667 := by norm_num

private theorem prime_thirtyFiveAG_10687 : Nat.Prime 10687 := by norm_num

private theorem prime_thirtyFiveAG_10909 : Nat.Prime 10909 := by norm_num

private theorem prime_thirtyFiveAG_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_thirtyFiveAG_11617 : Nat.Prime 11617 := by norm_num

private theorem prime_thirtyFiveAG_11719 : Nat.Prime 11719 := by norm_num

private theorem prime_thirtyFiveAG_12107 : Nat.Prime 12107 := by norm_num

private theorem prime_thirtyFiveAG_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_thirtyFiveAG_12589 : Nat.Prime 12589 := by norm_num

private theorem prime_thirtyFiveAG_12743 : Nat.Prime 12743 := by norm_num

private theorem prime_thirtyFiveAG_12907 : Nat.Prime 12907 := by norm_num

private theorem prime_thirtyFiveAG_13099 : Nat.Prime 13099 := by norm_num

private theorem prime_thirtyFiveAG_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_thirtyFiveAG_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_thirtyFiveAG_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_thirtyFiveAG_14083 : Nat.Prime 14083 := by norm_num

private theorem prime_thirtyFiveAG_15073 : Nat.Prime 15073 := by norm_num

private theorem prime_thirtyFiveAG_15299 : Nat.Prime 15299 := by norm_num

private theorem prime_thirtyFiveAG_15349 : Nat.Prime 15349 := by norm_num

private theorem prime_thirtyFiveAG_15383 : Nat.Prime 15383 := by norm_num

private theorem prime_thirtyFiveAG_15497 : Nat.Prime 15497 := by norm_num

private theorem prime_thirtyFiveAG_15643 : Nat.Prime 15643 := by norm_num

private theorem prime_thirtyFiveAG_15661 : Nat.Prime 15661 := by norm_num

private theorem prime_thirtyFiveAG_16693 : Nat.Prime 16693 := by norm_num

private theorem prime_thirtyFiveAG_19009 : Nat.Prime 19009 := by norm_num

private theorem prime_thirtyFiveAG_19379 : Nat.Prime 19379 := by norm_num

private theorem prime_thirtyFiveAG_19597 : Nat.Prime 19597 := by norm_num

private theorem prime_thirtyFiveAG_19997 : Nat.Prime 19997 := by norm_num

private theorem prime_thirtyFiveAG_20389 : Nat.Prime 20389 := by norm_num

private theorem prime_thirtyFiveAG_21163 : Nat.Prime 21163 := by norm_num

private theorem prime_thirtyFiveAG_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_thirtyFiveAG_21517 : Nat.Prime 21517 := by norm_num

private theorem prime_thirtyFiveAG_22273 : Nat.Prime 22273 := by norm_num

private theorem prime_thirtyFiveAG_22279 : Nat.Prime 22279 := by norm_num

private theorem prime_thirtyFiveAG_23011 : Nat.Prime 23011 := by norm_num

private theorem prime_thirtyFiveAG_23081 : Nat.Prime 23081 := by norm_num

private theorem prime_thirtyFiveAG_23131 : Nat.Prime 23131 := by norm_num

private theorem prime_thirtyFiveAG_27743 : Nat.Prime 27743 := by norm_num

private theorem prime_thirtyFiveAG_28429 : Nat.Prime 28429 := by norm_num

private theorem prime_thirtyFiveAG_29921 : Nat.Prime 29921 := by norm_num

private theorem prime_thirtyFiveAG_30011 : Nat.Prime 30011 := by norm_num

private theorem prime_thirtyFiveAG_30071 : Nat.Prime 30071 := by norm_num

private theorem prime_thirtyFiveAG_30103 : Nat.Prime 30103 := by norm_num

private theorem prime_thirtyFiveAG_33809 : Nat.Prime 33809 := by norm_num

private theorem prime_thirtyFiveAG_33811 : Nat.Prime 33811 := by norm_num

private theorem prime_thirtyFiveAG_34217 : Nat.Prime 34217 := by norm_num

private theorem prime_thirtyFiveAG_36551 : Nat.Prime 36551 := by norm_num

private theorem prime_thirtyFiveAG_36899 : Nat.Prime 36899 := by norm_num

private theorem prime_thirtyFiveAG_37039 : Nat.Prime 37039 := by norm_num

private theorem prime_thirtyFiveAG_40123 : Nat.Prime 40123 := by norm_num

private theorem prime_thirtyFiveAG_41621 : Nat.Prime 41621 := by norm_num

private theorem prime_thirtyFiveAG_41911 : Nat.Prime 41911 := by norm_num

private theorem prime_thirtyFiveAG_42787 : Nat.Prime 42787 := by norm_num

private theorem prime_thirtyFiveAG_43591 : Nat.Prime 43591 := by norm_num

private theorem prime_thirtyFiveAG_46567 : Nat.Prime 46567 := by norm_num

private theorem prime_thirtyFiveAG_47387 : Nat.Prime 47387 := by norm_num

private theorem prime_thirtyFiveAG_50261 : Nat.Prime 50261 := by norm_num

private theorem prime_thirtyFiveAG_54421 : Nat.Prime 54421 := by norm_num

private theorem prime_thirtyFiveAG_54623 : Nat.Prime 54623 := by norm_num

private theorem prime_thirtyFiveAG_56431 : Nat.Prime 56431 := by norm_num

private theorem prime_thirtyFiveAG_64153 : Nat.Prime 64153 := by norm_num

private theorem prime_thirtyFiveAG_64399 : Nat.Prime 64399 := by norm_num

private theorem prime_thirtyFiveAG_64679 : Nat.Prime 64679 := by norm_num

private theorem prime_thirtyFiveAG_65657 : Nat.Prime 65657 := by norm_num

private theorem prime_thirtyFiveAG_65983 : Nat.Prime 65983 := by norm_num

private theorem prime_thirtyFiveAG_72973 : Nat.Prime 72973 := by norm_num

private theorem prime_thirtyFiveAG_75653 : Nat.Prime 75653 := by norm_num

private theorem prime_thirtyFiveAG_78283 : Nat.Prime 78283 := by norm_num

private theorem prime_thirtyFiveAG_85303 : Nat.Prime 85303 := by norm_num

private theorem prime_thirtyFiveAG_86477 : Nat.Prime 86477 := by norm_num

private theorem prime_thirtyFiveAG_88471 : Nat.Prime 88471 := by norm_num

private theorem prime_thirtyFiveAG_89237 : Nat.Prime 89237 := by norm_num

private theorem prime_thirtyFiveAG_99611 : Nat.Prime 99611 := by norm_num

private theorem prime_thirtyFiveAG_101287 : Nat.Prime 101287 := by norm_num

private theorem prime_thirtyFiveAG_111509 : Nat.Prime 111509 := by norm_num

private theorem prime_thirtyFiveAG_113437 : Nat.Prime 113437 := by norm_num

private theorem prime_thirtyFiveAG_114761 : Nat.Prime 114761 := by norm_num

private theorem prime_thirtyFiveAG_118787 : Nat.Prime 118787 := by norm_num

private theorem prime_thirtyFiveAG_127487 : Nat.Prime 127487 := by norm_num

private theorem prime_thirtyFiveAG_132661 : Nat.Prime 132661 := by norm_num

private theorem prime_thirtyFiveAG_136949 : Nat.Prime 136949 := by norm_num

private theorem prime_thirtyFiveAG_143669 : Nat.Prime 143669 := by norm_num

private theorem prime_thirtyFiveAG_149441 : Nat.Prime 149441 := by norm_num

private theorem prime_thirtyFiveAG_157889 : Nat.Prime 157889 := by norm_num

private theorem prime_thirtyFiveAG_158519 : Nat.Prime 158519 := by norm_num

private theorem prime_thirtyFiveAG_159293 : Nat.Prime 159293 := by norm_num

private theorem prime_thirtyFiveAG_173293 : Nat.Prime 173293 := by norm_num

private theorem prime_thirtyFiveAG_176857 : Nat.Prime 176857 := by norm_num

private theorem prime_thirtyFiveAG_186023 : Nat.Prime 186023 := by norm_num

private theorem prime_thirtyFiveAG_189853 : Nat.Prime 189853 := by norm_num

private theorem prime_thirtyFiveAG_192007 : Nat.Prime 192007 := by norm_num

private theorem prime_thirtyFiveAG_195271 : Nat.Prime 195271 := by norm_num

private theorem prime_thirtyFiveAG_207017 : Nat.Prime 207017 := by norm_num

private theorem prime_thirtyFiveAG_220471 : Nat.Prime 220471 := by norm_num

private theorem prime_thirtyFiveAG_223543 : Nat.Prime 223543 := by norm_num

private theorem prime_thirtyFiveAG_225611 : Nat.Prime 225611 := by norm_num

private theorem prime_thirtyFiveAG_250049 : Nat.Prime 250049 := by norm_num

private theorem prime_thirtyFiveAG_293147 : Nat.Prime 293147 := by norm_num

private theorem prime_thirtyFiveAG_311299 : Nat.Prime 311299 := by norm_num

private theorem prime_thirtyFiveAG_311677 : Nat.Prime 311677 := by norm_num

private theorem prime_thirtyFiveAG_316097 : Nat.Prime 316097 := by norm_num

private theorem prime_thirtyFiveAG_329083 : Nat.Prime 329083 := by norm_num

private theorem prime_thirtyFiveAG_330241 : Nat.Prime 330241 := by norm_num

private theorem prime_thirtyFiveAG_343559 : Nat.Prime 343559 := by norm_num

private theorem prime_thirtyFiveAG_350351 : Nat.Prime 350351 := by norm_num

private theorem prime_thirtyFiveAG_363611 : Nat.Prime 363611 := by norm_num

private theorem prime_thirtyFiveAG_367219 : Nat.Prime 367219 := by norm_num

private theorem prime_thirtyFiveAG_381559 : Nat.Prime 381559 := by norm_num

private theorem prime_thirtyFiveAG_387551 : Nat.Prime 387551 := by norm_num

private theorem prime_thirtyFiveAG_413869 : Nat.Prime 413869 := by norm_num

private theorem prime_thirtyFiveAG_415153 : Nat.Prime 415153 := by norm_num

private theorem prime_thirtyFiveAG_415517 : Nat.Prime 415517 := by norm_num

private theorem prime_thirtyFiveAG_416147 : Nat.Prime 416147 := by norm_num

private theorem prime_thirtyFiveAG_431891 : Nat.Prime 431891 := by norm_num

private theorem prime_thirtyFiveAG_463511 : Nat.Prime 463511 := by norm_num

private theorem prime_thirtyFiveAG_558757 : Nat.Prime 558757 := by norm_num

private theorem prime_thirtyFiveAG_562501 : Nat.Prime 562501 := by norm_num

private theorem prime_thirtyFiveAG_568679 : Nat.Prime 568679 := by norm_num

private theorem prime_thirtyFiveAG_576509 : Nat.Prime 576509 := by norm_num

private theorem prime_thirtyFiveAG_587771 : Nat.Prime 587771 := by norm_num

private theorem prime_thirtyFiveAG_608411 : Nat.Prime 608411 := by norm_num

private theorem prime_thirtyFiveAG_640127 : Nat.Prime 640127 := by norm_num

private theorem prime_thirtyFiveAG_656951 : Nat.Prime 656951 := by norm_num

private theorem prime_thirtyFiveAG_689341 : Nat.Prime 689341 := by norm_num

private theorem prime_thirtyFiveAG_762563 : Nat.Prime 762563 := by norm_num

private theorem prime_thirtyFiveAG_789227 : Nat.Prime 789227 := by norm_num

private theorem prime_thirtyFiveAG_906371 : Nat.Prime 906371 := by norm_num

private theorem prime_thirtyFiveAG_975629 : Nat.Prime 975629 := by norm_num

private theorem prime_thirtyFiveAG_989347 : Nat.Prime 989347 := by norm_num

private theorem prime_thirtyFiveAG_1071571 : Nat.Prime 1071571 := by norm_num

private theorem prime_thirtyFiveAG_1169683 : Nat.Prime 1169683 := by norm_num

private theorem prime_thirtyFiveAG_1173959 : Nat.Prime 1173959 := by norm_num

private theorem prime_thirtyFiveAG_1214167 : Nat.Prime 1214167 := by norm_num

private theorem prime_thirtyFiveAG_1216729 : Nat.Prime 1216729 := by norm_num

private theorem prime_thirtyFiveAG_1277791 : Nat.Prime 1277791 := by norm_num

private theorem prime_thirtyFiveAG_1346333 : Nat.Prime 1346333 := by norm_num

private theorem prime_thirtyFiveAG_1406557 : Nat.Prime 1406557 := by norm_num

private theorem prime_thirtyFiveAG_1433741 : Nat.Prime 1433741 := by norm_num

private theorem prime_thirtyFiveAG_1489003 : Nat.Prime 1489003 := by norm_num

private theorem prime_thirtyFiveAG_1498121 : Nat.Prime 1498121 := by norm_num

private theorem prime_thirtyFiveAG_1541597 : Nat.Prime 1541597 := by norm_num

private theorem prime_thirtyFiveAG_1544987 : Nat.Prime 1544987 := by norm_num

private theorem prime_thirtyFiveAG_1693169 : Nat.Prime 1693169 := by norm_num

private theorem prime_thirtyFiveAG_1788539 : Nat.Prime 1788539 := by norm_num

private theorem prime_thirtyFiveAG_1820969 : Nat.Prime 1820969 := by norm_num

private theorem prime_thirtyFiveAG_1957301 : Nat.Prime 1957301 := by norm_num

private theorem prime_thirtyFiveAG_1965263 : Nat.Prime 1965263 := by norm_num

private theorem prime_thirtyFiveAG_2026751 : Nat.Prime 2026751 := by norm_num

private theorem prime_thirtyFiveAG_2100227 : Nat.Prime 2100227 := by norm_num

private theorem prime_thirtyFiveAG_2201209 : Nat.Prime 2201209 := by norm_num

private theorem prime_thirtyFiveAG_2205803 : Nat.Prime 2205803 := by norm_num

private theorem prime_thirtyFiveAG_2227409 : Nat.Prime 2227409 := by norm_num

private theorem prime_thirtyFiveAG_2409709 : Nat.Prime 2409709 := by norm_num

private theorem prime_thirtyFiveAG_2567303 : Nat.Prime 2567303 := by norm_num

private theorem prime_thirtyFiveAG_2633923 : Nat.Prime 2633923 := by norm_num

private theorem prime_thirtyFiveAG_2669767 : Nat.Prime 2669767 := by norm_num

private theorem prime_thirtyFiveAG_2846287 : Nat.Prime 2846287 := by norm_num

private theorem prime_thirtyFiveAG_2924183 : Nat.Prime 2924183 := by norm_num

private theorem prime_thirtyFiveAG_3355031 : Nat.Prime 3355031 := by norm_num

private theorem prime_thirtyFiveAG_3439229 : Nat.Prime 3439229 := by norm_num

private theorem prime_thirtyFiveAG_3532679 : Nat.Prime 3532679 := by norm_num

private theorem prime_thirtyFiveAG_3779417 : Nat.Prime 3779417 := by norm_num

private theorem prime_thirtyFiveAG_4089619 : Nat.Prime 4089619 := by norm_num

private theorem prime_thirtyFiveAG_4509013 : Nat.Prime 4509013 := by norm_num

private theorem prime_thirtyFiveAG_4614439 : Nat.Prime 4614439 := by norm_num

private theorem prime_thirtyFiveAG_5210423 : Nat.Prime 5210423 := by norm_num

private theorem prime_thirtyFiveAG_5601139 : Nat.Prime 5601139 := by norm_num

private theorem prime_thirtyFiveAG_5977651 : Nat.Prime 5977651 := by norm_num

private theorem prime_thirtyFiveAG_6070121 : Nat.Prime 6070121 := by norm_num

private theorem prime_thirtyFiveAG_6470753 : Nat.Prime 6470753 := by norm_num

private theorem prime_thirtyFiveAG_6475879 : Nat.Prime 6475879 := by norm_num

private theorem prime_thirtyFiveAG_6515723 : Nat.Prime 6515723 := by norm_num

private theorem prime_thirtyFiveAG_7508069 : Nat.Prime 7508069 := by norm_num

private theorem prime_thirtyFiveAG_7787971 : Nat.Prime 7787971 := by norm_num

private theorem prime_thirtyFiveAG_7978459 : Nat.Prime 7978459 := by norm_num

private theorem prime_thirtyFiveAG_9211919 : Nat.Prime 9211919 := by norm_num

private theorem prime_thirtyFiveAG_9690287 : Nat.Prime 9690287 := by norm_num

private theorem prime_thirtyFiveAG_9813829 : Nat.Prime 9813829 := by norm_num

private theorem prime_thirtyFiveAG_9985499 : Nat.Prime 9985499 := by norm_num

private theorem prime_thirtyFiveAG_10715711 : Nat.Prime 10715711 := by
  apply lucas_primality 10715711 (13 : ZMod 10715711)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1071571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1071571, 1)] : List FactorBlock).map factorBlockValue).prod) = 10715711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_1071571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 10715711) ^ 5357855 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 10715711) ^ 2143142 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 10715711) ^ 10 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11422337 : Nat.Prime 11422337 := by
  apply lucas_primality 11422337 (3 : ZMod 11422337)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (89237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (89237, 1)] : List FactorBlock).map factorBlockValue).prod) = 11422337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_89237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11422337) ^ 5711168 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11422337) ^ 128 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11564851 : Nat.Prime 11564851 := by
  apply lucas_primality 11564851 (2 : ZMod 11564851)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (43, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (43, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 11564851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_43
      · exact prime_t64_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11564851) ^ 5782425 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11564851) ^ 3854950 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11564851) ^ 2312970 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11564851) ^ 1051350 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11564851) ^ 268950 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11564851) ^ 70950 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13190773 : Nat.Prime 13190773 := by
  apply lucas_primality 13190773 (5 : ZMod 13190773)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (373, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (373, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 13190773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_373
      · exact prime_t64_421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13190773) ^ 6595386 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 13190773) ^ 4396924 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 13190773) ^ 1884396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 13190773) ^ 35364 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 13190773) ^ 31332 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13402009 : Nat.Prime 13402009 := by
  apply lucas_primality 13402009 (7 : ZMod 13402009)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (8093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (8093, 1)] : List FactorBlock).map factorBlockValue).prod) = 13402009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_8093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13402009) ^ 6701004 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 13402009) ^ 4467336 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 13402009) ^ 582696 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 13402009) ^ 1656 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13737811 : Nat.Prime 13737811 := by
  apply lucas_primality 13737811 (3 : ZMod 13737811)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_7507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13737811) ^ 6868905 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 4579270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 2747562 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 225210 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737811) ^ 1830 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_14719189 : Nat.Prime 14719189 := by
  apply lucas_primality 14719189 (6 : ZMod 14719189)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_111509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14719189) ^ 7359594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 4906396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 1338108 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 14719189) ^ 132 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_15546227 : Nat.Prime 15546227 := by
  apply lucas_primality 15546227 (2 : ZMod 15546227)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (233, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (233, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 15546227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_73
      · exact prime_t64_233
      · exact prime_thirtyFiveAG_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15546227) ^ 7773113 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15546227) ^ 212962 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15546227) ^ 66722 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15546227) ^ 34018 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_15558227 : Nat.Prime 15558227 := by
  apply lucas_primality 15558227 (2 : ZMod 15558227)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15558227) ^ 7779113 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 818854 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 40622 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15558227) ^ 14554 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_16346527 : Nat.Prime 16346527 := by
  apply lucas_primality 16346527 (3 : ZMod 16346527)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (67, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (67, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 16346527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_t64_67
      · exact prime_t64_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16346527) ^ 8173263 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16346527) ^ 5448842 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16346527) ^ 2335218 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16346527) ^ 441798 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16346527) ^ 243978 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 16346527) ^ 104118 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_17317939 : Nat.Prime 17317939 := by
  apply lucas_primality 17317939 (2 : ZMod 17317939)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (131, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (131, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 17317939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_131
      · exact prime_thirtyFiveAG_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17317939) ^ 8658969 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17317939) ^ 5772646 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17317939) ^ 1574358 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17317939) ^ 132198 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17317939) ^ 8646 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_18132239 : Nat.Prime 18132239 := by
  apply lucas_primality 18132239 (11 : ZMod 18132239)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (114761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (114761, 1)] : List FactorBlock).map factorBlockValue).prod) = 18132239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_thirtyFiveAG_114761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 18132239) ^ 9066119 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 18132239) ^ 229522 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 18132239) ^ 158 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_18547957 : Nat.Prime 18547957 := by
  apply lucas_primality 18547957 (5 : ZMod 18547957)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (89, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (89, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) = 18547957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_thirtyFiveAG_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18547957) ^ 9273978 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18547957) ^ 6182652 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18547957) ^ 2649708 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18547957) ^ 208404 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18547957) ^ 22428 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20826023 : Nat.Prime 20826023 := by
  apply lucas_primality 20826023 (5 : ZMod 20826023)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1093, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1093, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) = 20826023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_1093
      · exact prime_thirtyFiveAG_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20826023) ^ 10413011 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20826023) ^ 2975146 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20826023) ^ 19054 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20826023) ^ 15302 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20869127 : Nat.Prime 20869127 := by
  apply lucas_primality 20869127 (5 : ZMod 20869127)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (176857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (176857, 1)] : List FactorBlock).map factorBlockValue).prod) = 20869127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_thirtyFiveAG_176857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20869127) ^ 10434563 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20869127) ^ 353714 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20869127) ^ 118 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_21276337 : Nat.Prime 21276337 := by
  apply lucas_primality 21276337 (5 : ZMod 21276337)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (9431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (9431, 1)] : List FactorBlock).map factorBlockValue).prod) = 21276337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_thirtyFiveAG_9431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21276337) ^ 10638168 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21276337) ^ 7092112 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21276337) ^ 452688 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21276337) ^ 2256 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_22283273 : Nat.Prime 22283273 := by
  apply lucas_primality 22283273 (3 : ZMod 22283273)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (181, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (181, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 22283273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_181
      · exact prime_thirtyFiveAG_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22283273) ^ 11141636 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22283273) ^ 2025752 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22283273) ^ 123112 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22283273) ^ 15928 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_22750313 : Nat.Prime 22750313 := by
  apply lucas_primality 22750313 (3 : ZMod 22750313)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (23, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (23, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) = 22750313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_9511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22750313) ^ 11375156 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22750313) ^ 1750024 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22750313) ^ 989144 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22750313) ^ 2392 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_22951043 : Nat.Prime 22951043 := by
  apply lucas_primality 22951043 (2 : ZMod 22951043)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1303, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) = 22951043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_1303
      · exact prime_thirtyFiveAG_8807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22951043) ^ 11475521 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 17614 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951043) ^ 2606 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_23608747 : Nat.Prime 23608747 := by
  apply lucas_primality 23608747 (2 : ZMod 23608747)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (109, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (109, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 23608747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_109
      · exact prime_t64_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23608747) ^ 11804373 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23608747) ^ 7869582 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23608747) ^ 3372678 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23608747) ^ 216594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23608747) ^ 123606 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_23612227 : Nat.Prime 23612227 := by
  apply lucas_primality 23612227 (5 : ZMod 23612227)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (131, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (131, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 23612227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_131
      · exact prime_thirtyFiveAG_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23612227) ^ 11806113 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23612227) ^ 7870742 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23612227) ^ 2146566 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23612227) ^ 180246 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 23612227) ^ 8646 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_23622671 : Nat.Prime 23622671 := by
  apply lucas_primality 23622671 (7 : ZMod 23622671)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_50261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 23622671) ^ 11811335 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 4724534 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 502610 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 23622671) ^ 470 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_23693977 : Nat.Prime 23693977 := by
  apply lucas_primality 23693977 (7 : ZMod 23693977)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (329083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (329083, 1)] : List FactorBlock).map factorBlockValue).prod) = 23693977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_329083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 23693977) ^ 11846988 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 23693977) ^ 7897992 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 23693977) ^ 72 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_25830341 : Nat.Prime 25830341 := by
  apply lucas_primality 25830341 (2 : ZMod 25830341)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (12539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (12539, 1)] : List FactorBlock).map factorBlockValue).prod) = 25830341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_103
      · exact prime_thirtyFiveAG_12539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25830341) ^ 12915170 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25830341) ^ 5166068 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25830341) ^ 250780 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25830341) ^ 2060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_29801971 : Nat.Prime 29801971 := by
  apply lucas_primality 29801971 (3 : ZMod 29801971)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (30103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (30103, 1)] : List FactorBlock).map factorBlockValue).prod) = 29801971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_30103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29801971) ^ 14900985 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 29801971) ^ 9933990 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 29801971) ^ 5960394 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 29801971) ^ 2709270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 29801971) ^ 990 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_36160427 : Nat.Prime 36160427 := by
  apply lucas_primality 36160427 (2 : ZMod 36160427)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (54623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (54623, 1)] : List FactorBlock).map factorBlockValue).prod) = 36160427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_331
      · exact prime_thirtyFiveAG_54623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36160427) ^ 18080213 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36160427) ^ 109246 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 36160427) ^ 662 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_36264479 : Nat.Prime 36264479 := by
  apply lucas_primality 36264479 (11 : ZMod 36264479)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18132239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18132239, 1)] : List FactorBlock).map factorBlockValue).prod) = 36264479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_18132239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 36264479) ^ 18132239 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 36264479) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_45213631 : Nat.Prime 45213631 := by
  apply lucas_primality 45213631 (11 : ZMod 45213631)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (23, 2), (37, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (23, 2), (37, 1)] : List FactorBlock).map factorBlockValue).prod) = 45213631 - 1 by
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
      · exact prime_t64_23
      · exact prime_t64_37
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 45213631) ^ 22606815 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 15071210 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 9042726 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 6459090 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 4110330 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 1965810 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 45213631) ^ 1221990 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_51660683 : Nat.Prime 51660683 := by
  apply lucas_primality 51660683 (2 : ZMod 51660683)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25830341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25830341, 1)] : List FactorBlock).map factorBlockValue).prod) = 51660683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_25830341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51660683) ^ 25830341 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51660683) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_56262281 : Nat.Prime 56262281 := by
  apply lucas_primality 56262281 (3 : ZMod 56262281)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1406557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1406557, 1)] : List FactorBlock).map factorBlockValue).prod) = 56262281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_1406557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56262281) ^ 28131140 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56262281) ^ 11252456 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56262281) ^ 40 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_63375941 : Nat.Prime 63375941 := by
  apply lucas_primality 63375941 (3 : ZMod 63375941)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1487, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1487, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 63375941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_1487
      · exact prime_thirtyFiveAG_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63375941) ^ 31687970 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63375941) ^ 12675188 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63375941) ^ 42620 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 63375941) ^ 29740 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_64043047 : Nat.Prime 64043047 := by
  apply lucas_primality 64043047 (3 : ZMod 64043047)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (47, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (47, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 64043047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_47
      · exact prime_t64_61
      · exact prime_t64_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64043047) ^ 32021523 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 64043047) ^ 21347682 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 64043047) ^ 3767238 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 64043047) ^ 1362618 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 64043047) ^ 1049886 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 64043047) ^ 877302 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_72974479 : Nat.Prime 72974479 := by
  apply lucas_primality 72974479 (3 : ZMod 72974479)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (640127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (640127, 1)] : List FactorBlock).map factorBlockValue).prod) = 72974479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_640127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72974479) ^ 36487239 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72974479) ^ 24324826 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72974479) ^ 3840762 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72974479) ^ 114 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_77303803 : Nat.Prime 77303803 := by
  apply lucas_primality 77303803 (2 : ZMod 77303803)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (557, 1), (23131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (557, 1), (23131, 1)] : List FactorBlock).map factorBlockValue).prod) = 77303803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_557
      · exact prime_thirtyFiveAG_23131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77303803) ^ 38651901 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77303803) ^ 25767934 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77303803) ^ 138786 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77303803) ^ 3342 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_136501879 : Nat.Prime 136501879 := by
  apply lucas_primality 136501879 (3 : ZMod 136501879)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22750313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22750313, 1)] : List FactorBlock).map factorBlockValue).prod) = 136501879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_22750313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 136501879) ^ 68250939 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136501879) ^ 45500626 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136501879) ^ 6 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_156970531 : Nat.Prime 156970531 := by
  apply lucas_primality 156970531 (2 : ZMod 156970531)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (241, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (241, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 156970531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_241
      · exact prime_thirtyFiveAG_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156970531) ^ 78485265 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 156970531) ^ 52323510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 156970531) ^ 31394106 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 156970531) ^ 651330 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 156970531) ^ 21690 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_188801429 : Nat.Prime 188801429 := by
  apply lucas_primality 188801429 (2 : ZMod 188801429)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (568679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (568679, 1)] : List FactorBlock).map factorBlockValue).prod) = 188801429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_83
      · exact prime_thirtyFiveAG_568679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 188801429) ^ 94400714 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 188801429) ^ 2274716 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 188801429) ^ 332 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_197258651 : Nat.Prime 197258651 := by
  apply lucas_primality 197258651 (2 : ZMod 197258651)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (239, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (239, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 197258651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_239
      · exact prime_thirtyFiveAG_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 197258651) ^ 98629325 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 197258651) ^ 39451730 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 197258651) ^ 11603450 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 197258651) ^ 825350 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 197258651) ^ 203150 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_236939771 : Nat.Prime 236939771 := by
  apply lucas_primality 236939771 (2 : ZMod 236939771)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23693977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23693977, 1)] : List FactorBlock).map factorBlockValue).prod) = 236939771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_23693977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 236939771) ^ 118469885 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 236939771) ^ 47387954 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 236939771) ^ 10 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_247757789 : Nat.Prime 247757789 := by
  apply lucas_primality 247757789 (2 : ZMod 247757789)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 8543372 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 2554204 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 247757789) ^ 1091444 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_280497757 : Nat.Prime 280497757 := by
  apply lucas_primality 280497757 (2 : ZMod 280497757)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 1), (17, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 1), (17, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 280497757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_thirtyFiveAG_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 280497757) ^ 140248878 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 280497757) ^ 93499252 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 280497757) ^ 40071108 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 280497757) ^ 25499796 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 280497757) ^ 16499868 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 280497757) ^ 109956 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_321206161 : Nat.Prime 321206161 := by
  apply lucas_primality 321206161 (29 : ZMod 321206161)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (17, 2), (421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (17, 2), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 321206161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 321206161) ^ 160603080 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 321206161) ^ 107068720 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 321206161) ^ 64241232 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 321206161) ^ 29200560 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 321206161) ^ 18894480 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 321206161) ^ 762960 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_356006269 : Nat.Prime 356006269 := by
  apply lucas_primality 356006269 (10 : ZMod 356006269)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (263, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (263, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) = 356006269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_263
      · exact prime_thirtyFiveAG_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 356006269) ^ 178003134 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 356006269) ^ 118668756 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 356006269) ^ 18737172 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 356006269) ^ 1353636 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 356006269) ^ 179892 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_366269941 : Nat.Prime 366269941 := by
  apply lucas_primality 366269941 (2 : ZMod 366269941)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (23, 1), (88471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (23, 1), (88471, 1)] : List FactorBlock).map factorBlockValue).prod) = 366269941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_88471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 366269941) ^ 183134970 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366269941) ^ 122089980 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366269941) ^ 73253988 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366269941) ^ 15924780 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 366269941) ^ 4140 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_381350491 : Nat.Prime 381350491 := by
  apply lucas_primality 381350491 (2 : ZMod 381350491)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) = 381350491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_thirtyFiveAG_343559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381350491) ^ 190675245 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 127116830 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 76270098 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 10306770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 1110 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_453090653 : Nat.Prime 453090653 := by
  apply lucas_primality 453090653 (2 : ZMod 453090653)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (330241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (330241, 1)] : List FactorBlock).map factorBlockValue).prod) = 453090653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_330241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 453090653) ^ 226545326 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 453090653) ^ 64727236 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 453090653) ^ 1372 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_463822819 : Nat.Prime 463822819 := by
  apply lucas_primality 463822819 (3 : ZMod 463822819)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (77303803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (77303803, 1)] : List FactorBlock).map factorBlockValue).prod) = 463822819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_77303803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 463822819) ^ 231911409 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 463822819) ^ 154607606 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 463822819) ^ 6 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_485243849 : Nat.Prime 485243849 := by
  apply lucas_primality 485243849 (3 : ZMod 485243849)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (73, 1), (14083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (73, 1), (14083, 1)] : List FactorBlock).map factorBlockValue).prod) = 485243849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_73
      · exact prime_thirtyFiveAG_14083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 485243849) ^ 242621924 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 485243849) ^ 8224472 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 485243849) ^ 6647176 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 485243849) ^ 34456 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_500452427 : Nat.Prime 500452427 := by
  apply lucas_primality 500452427 (2 : ZMod 500452427)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_14719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500452427) ^ 250226213 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 29438378 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 500452427) ^ 34 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_thirtyFiveAG_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_552255019 : Nat.Prime 552255019 := by
  apply lucas_primality 552255019 (2 : ZMod 552255019)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (53, 2), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (53, 2), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 552255019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 552255019) ^ 276127509 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552255019) ^ 184085006 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552255019) ^ 78893574 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552255019) ^ 17814678 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552255019) ^ 10419906 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 552255019) ^ 3657318 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_654477533 : Nat.Prime 654477533 := by
  apply lucas_primality 654477533 (2 : ZMod 654477533)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (353, 1), (463511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (353, 1), (463511, 1)] : List FactorBlock).map factorBlockValue).prod) = 654477533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_353
      · exact prime_thirtyFiveAG_463511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 654477533) ^ 327238766 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 654477533) ^ 1854044 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 654477533) ^ 1412 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_939009853 : Nat.Prime 939009853 := by
  apply lucas_primality 939009853 (5 : ZMod 939009853)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 3), (19597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 3), (19597, 1)] : List FactorBlock).map factorBlockValue).prod) = 939009853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_19597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 939009853) ^ 469504926 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 939009853) ^ 313003284 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 939009853) ^ 85364532 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 939009853) ^ 47916 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1125245621 : Nat.Prime 1125245621 := by
  apply lucas_primality 1125245621 (2 : ZMod 1125245621)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (56262281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (56262281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1125245621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_56262281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1125245621) ^ 562622810 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1125245621) ^ 225049124 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1125245621) ^ 20 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1165447333 : Nat.Prime 1165447333 := by
  apply lucas_primality 1165447333 (5 : ZMod 1165447333)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (1541597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (1541597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1165447333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_1541597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1165447333) ^ 582723666 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1165447333) ^ 388482444 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1165447333) ^ 166492476 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1165447333) ^ 756 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1256896603 : Nat.Prime 1256896603 := by
  apply lucas_primality 1256896603 (5 : ZMod 1256896603)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (13, 2), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (13, 2), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256896603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_5101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1256896603) ^ 628448301 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1256896603) ^ 418965534 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1256896603) ^ 96684354 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1256896603) ^ 246402 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1308379129 : Nat.Prime 1308379129 := by
  apply lucas_primality 1308379129 (19 : ZMod 1308379129)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (7787971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (7787971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308379129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_7787971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 1308379129) ^ 654189564 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (19 : ZMod 1308379129) ^ 436126376 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (19 : ZMod 1308379129) ^ 186911304 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (19 : ZMod 1308379129) ^ 168 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1314572993 : Nat.Prime 1314572993 := by
  apply lucas_primality 1314572993 (3 : ZMod 1314572993)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (53, 1), (387551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (53, 1), (387551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1314572993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_387551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1314572993) ^ 657286496 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1314572993) ^ 24803264 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1314572993) ^ 3392 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1439312431 : Nat.Prime 1439312431 := by
  apply lucas_primality 1439312431 (3 : ZMod 1439312431)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3067, 1), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3067, 1), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439312431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_3067
      · exact prime_thirtyFiveAG_15643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1439312431) ^ 719656215 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439312431) ^ 479770810 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439312431) ^ 287862486 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439312431) ^ 469290 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439312431) ^ 92010 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1505045441 : Nat.Prime 1505045441 := by
  apply lucas_primality 1505045441 (3 : ZMod 1505045441)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (101, 1), (46567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (101, 1), (46567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1505045441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_101
      · exact prime_thirtyFiveAG_46567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1505045441) ^ 752522720 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505045441) ^ 301009088 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505045441) ^ 14901440 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505045441) ^ 32320 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1510411433 : Nat.Prime 1510411433 := by
  apply lucas_primality 1510411433 (3 : ZMod 1510411433)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (188801429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (188801429, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510411433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_188801429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1510411433) ^ 755205716 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1510411433) ^ 8 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1531293541 : Nat.Prime 1531293541 := by
  apply lucas_primality 1531293541 (2 : ZMod 1531293541)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (158519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (158519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531293541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_158519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1531293541) ^ 765646770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1531293541) ^ 510431180 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1531293541) ^ 306258708 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1531293541) ^ 218756220 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1531293541) ^ 66577980 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1531293541) ^ 9660 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1671268889 : Nat.Prime 1671268889 := by
  apply lucas_primality 1671268889 (3 : ZMod 1671268889)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_443
      · exact prime_t64_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1671268889) ^ 835634444 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 4086232 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 3772616 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1671268889) ^ 1449496 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3080754007 : Nat.Prime 3080754007 := by
  apply lucas_primality 3080754007 (3 : ZMod 3080754007)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (823, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (823, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 3080754007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_43
      · exact prime_thirtyFiveAG_823
      · exact prime_thirtyFiveAG_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3080754007) ^ 1540377003 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3080754007) ^ 1026918002 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3080754007) ^ 280068546 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3080754007) ^ 71645442 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3080754007) ^ 3743322 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3080754007) ^ 2335674 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_359
      · exact prime_thirtyFiveAG_677
      · exact prime_thirtyFiveAG_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3485277163 : Nat.Prime 3485277163 := by
  apply lucas_primality 3485277163 (3 : ZMod 3485277163)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8389, 1), (23081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8389, 1), (23081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3485277163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_8389
      · exact prime_thirtyFiveAG_23081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3485277163) ^ 1742638581 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3485277163) ^ 1161759054 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3485277163) ^ 415458 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3485277163) ^ 151002 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3813504911 : Nat.Prime 3813504911 := by
  apply lucas_primality 3813504911 (17 : ZMod 3813504911)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3813504911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_381350491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3813504911) ^ 1906752455 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 762700982 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 10 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_4829538607 : Nat.Prime 4829538607 := by
  apply lucas_primality 4829538607 (6 : ZMod 4829538607)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (431, 1), (64399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (431, 1), (64399, 1)] : List FactorBlock).map factorBlockValue).prod) = 4829538607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_431
      · exact prime_thirtyFiveAG_64399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4829538607) ^ 2414769303 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4829538607) ^ 1609846202 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4829538607) ^ 166535814 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4829538607) ^ 11205426 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4829538607) ^ 74994 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5822926189 : Nat.Prime 5822926189 := by
  apply lucas_primality 5822926189 (6 : ZMod 5822926189)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (485243849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (485243849, 1)] : List FactorBlock).map factorBlockValue).prod) = 5822926189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_485243849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5822926189) ^ 2911463094 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5822926189) ^ 1940975396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5822926189) ^ 12 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_6277125343 : Nat.Prime 6277125343 := by
  apply lucas_primality 6277125343 (5 : ZMod 6277125343)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (149, 1), (12743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (149, 1), (12743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6277125343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_29
      · exact prime_t64_149
      · exact prime_thirtyFiveAG_12743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6277125343) ^ 3138562671 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277125343) ^ 2092375114 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277125343) ^ 330375018 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277125343) ^ 216452598 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277125343) ^ 42128358 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277125343) ^ 492594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_7541379619 : Nat.Prime 7541379619 := by
  apply lucas_primality 7541379619 (2 : ZMod 7541379619)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1256896603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1256896603, 1)] : List FactorBlock).map factorBlockValue).prod) = 7541379619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_1256896603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7541379619) ^ 3770689809 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7541379619) ^ 2513793206 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7541379619) ^ 6 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_8138909897 : Nat.Prime 8138909897 := by
  apply lucas_primality 8138909897 (3 : ZMod 8138909897)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (8291, 1), (9439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (8291, 1), (9439, 1)] : List FactorBlock).map factorBlockValue).prod) = 8138909897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_8291
      · exact prime_thirtyFiveAG_9439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8138909897) ^ 4069454948 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138909897) ^ 626069992 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138909897) ^ 981656 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138909897) ^ 862264 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_8771383441 : Nat.Prime 8771383441 := by
  apply lucas_primality 8771383441 (11 : ZMod 8771383441)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (19, 1), (421, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (19, 1), (421, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 8771383441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_421
      · exact prime_thirtyFiveAG_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8771383441) ^ 4385691720 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 8771383441) ^ 2923794480 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 8771383441) ^ 1754276688 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 8771383441) ^ 461651760 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 8771383441) ^ 20834640 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 8771383441) ^ 5759280 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_10912459697 : Nat.Prime 10912459697 := by
  apply lucas_primality 10912459697 (3 : ZMod 10912459697)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (59, 1), (608411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (59, 1), (608411, 1)] : List FactorBlock).map factorBlockValue).prod) = 10912459697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_59
      · exact prime_thirtyFiveAG_608411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10912459697) ^ 5456229848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10912459697) ^ 574339984 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10912459697) ^ 184956944 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10912459697) ^ 17936 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_10987937171 : Nat.Prime 10987937171 := by
  apply lucas_primality 10987937171 (2 : ZMod 10987937171)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (156970531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (156970531, 1)] : List FactorBlock).map factorBlockValue).prod) = 10987937171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_156970531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10987937171) ^ 5493968585 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10987937171) ^ 2197587434 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10987937171) ^ 1569705310 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10987937171) ^ 70 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11001104683 : Nat.Prime 11001104683 := by
  apply lucas_primality 11001104683 (2 : ZMod 11001104683)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (13190773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (13190773, 1)] : List FactorBlock).map factorBlockValue).prod) = 11001104683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_139
      · exact prime_thirtyFiveAG_13190773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11001104683) ^ 5500552341 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11001104683) ^ 3667034894 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11001104683) ^ 79144638 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11001104683) ^ 834 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11842387189 : Nat.Prime 11842387189 := by
  apply lucas_primality 11842387189 (2 : ZMod 11842387189)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_15383
      · exact prime_thirtyFiveAG_64153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11842387189) ^ 5921193594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 3947462396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 769836 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11842387189) ^ 184596 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11935203661 : Nat.Prime 11935203661 := by
  apply lucas_primality 11935203661 (6 : ZMod 11935203661)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (71, 1), (311299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (71, 1), (311299, 1)] : List FactorBlock).map factorBlockValue).prod) = 11935203661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_thirtyFiveAG_311299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11935203661) ^ 5967601830 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11935203661) ^ 3978401220 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11935203661) ^ 2387040732 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11935203661) ^ 168101460 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 11935203661) ^ 38340 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_12733696831 : Nat.Prime 12733696831 := by
  apply lucas_primality 12733696831 (3 : ZMod 12733696831)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (59, 1), (22273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (59, 1), (22273, 1)] : List FactorBlock).map factorBlockValue).prod) = 12733696831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_59
      · exact prime_thirtyFiveAG_22273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12733696831) ^ 6366848415 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 4244565610 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 2546739366 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 749040990 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 670194570 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 215825370 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12733696831) ^ 571710 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_12831176627 : Nat.Prime 12831176627 := by
  apply lucas_primality 12831176627 (2 : ZMod 12831176627)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (136501879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (136501879, 1)] : List FactorBlock).map factorBlockValue).prod) = 12831176627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_thirtyFiveAG_136501879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12831176627) ^ 6415588313 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831176627) ^ 273003758 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12831176627) ^ 94 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_619
      · exact prime_thirtyFiveAG_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_14567263097 : Nat.Prime 14567263097 := by
  apply lucas_primality 14567263097 (3 : ZMod 14567263097)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (599, 1), (64679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (599, 1), (64679, 1)] : List FactorBlock).map factorBlockValue).prod) = 14567263097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_thirtyFiveAG_599
      · exact prime_thirtyFiveAG_64679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14567263097) ^ 7283631548 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14567263097) ^ 309941768 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14567263097) ^ 24319304 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14567263097) ^ 225224 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_16777701341 : Nat.Prime 16777701341 := by
  apply lucas_primality 16777701341 (2 : ZMod 16777701341)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (1289, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (1289, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) = 16777701341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_83
      · exact prime_thirtyFiveAG_1289
      · exact prime_thirtyFiveAG_7841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16777701341) ^ 8388850670 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 16777701341) ^ 3355540268 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 16777701341) ^ 202140980 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 16777701341) ^ 13016060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 16777701341) ^ 2139740 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_18304364483 : Nat.Prime 18304364483 := by
  apply lucas_primality 18304364483 (2 : ZMod 18304364483)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (677, 1), (587771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (677, 1), (587771, 1)] : List FactorBlock).map factorBlockValue).prod) = 18304364483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_677
      · exact prime_thirtyFiveAG_587771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18304364483) ^ 9152182241 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18304364483) ^ 795841934 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18304364483) ^ 27037466 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18304364483) ^ 31142 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20319607769 : Nat.Prime 20319607769 := by
  apply lucas_primality 20319607769 (3 : ZMod 20319607769)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) = 20319607769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_5881
      · exact prime_thirtyFiveAG_431891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20319607769) ^ 10159803884 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 3455128 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 47048 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20955128501 : Nat.Prime 20955128501 := by
  apply lucas_primality 20955128501 (2 : ZMod 20955128501)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (19, 1), (2205803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (19, 1), (2205803, 1)] : List FactorBlock).map factorBlockValue).prod) = 20955128501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_2205803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20955128501) ^ 10477564250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20955128501) ^ 4191025700 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20955128501) ^ 1102901500 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 20955128501) ^ 9500 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_21332805811 : Nat.Prime 21332805811 := by
  apply lucas_primality 21332805811 (2 : ZMod 21332805811)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (789227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (789227, 1)] : List FactorBlock).map factorBlockValue).prod) = 21332805811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_789227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21332805811) ^ 10666402905 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21332805811) ^ 7110935270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21332805811) ^ 4266561162 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21332805811) ^ 1254870930 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21332805811) ^ 402505770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21332805811) ^ 27030 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_487
      · exact prime_thirtyFiveAG_2621
      · exact prime_thirtyFiveAG_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_26687336297 : Nat.Prime 26687336297 := by
  apply lucas_primality 26687336297 (3 : ZMod 26687336297)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_21347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26687336297) ^ 13343668148 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 860881816 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 375877976 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 26687336297) ^ 1250168 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_34693855033 : Nat.Prime 34693855033 := by
  apply lucas_primality 34693855033 (7 : ZMod 34693855033)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (103, 1), (109, 1), (331, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (103, 1), (109, 1), (331, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 34693855033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_103
      · exact prime_t64_109
      · exact prime_thirtyFiveAG_331
      · exact prime_thirtyFiveAG_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 34693855033) ^ 17346927516 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34693855033) ^ 11564618344 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34693855033) ^ 336833544 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34693855033) ^ 318292248 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34693855033) ^ 104815272 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 34693855033) ^ 89187288 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_36608728967 : Nat.Prime 36608728967 := by
  apply lucas_primality 36608728967 (5 : ZMod 36608728967)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18304364483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18304364483, 1)] : List FactorBlock).map factorBlockValue).prod) = 36608728967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_18304364483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 36608728967) ^ 18304364483 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36608728967) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_37721539993 : Nat.Prime 37721539993 := by
  apply lucas_primality 37721539993 (5 : ZMod 37721539993)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (89, 1), (223543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (89, 1), (223543, 1)] : List FactorBlock).map factorBlockValue).prod) = 37721539993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_79
      · exact prime_t64_89
      · exact prime_thirtyFiveAG_223543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37721539993) ^ 18860769996 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 37721539993) ^ 12573846664 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 37721539993) ^ 477487848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 37721539993) ^ 423837528 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 37721539993) ^ 168744 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_38033471159 : Nat.Prime 38033471159 := by
  apply lucas_primality 38033471159 (13 : ZMod 38033471159)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (463822819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (463822819, 1)] : List FactorBlock).map factorBlockValue).prod) = 38033471159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_463822819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 38033471159) ^ 19016735579 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 38033471159) ^ 927645638 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 38033471159) ^ 82 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_44482396793 : Nat.Prime 44482396793 := by
  apply lucas_primality 44482396793 (3 : ZMod 44482396793)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (43, 1), (257, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (43, 1), (257, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 44482396793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_43
      · exact prime_thirtyFiveAG_257
      · exact prime_thirtyFiveAG_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44482396793) ^ 22241198396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 44482396793) ^ 2616611576 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 44482396793) ^ 1034474344 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 44482396793) ^ 173083256 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 44482396793) ^ 25549912 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_54977560373 : Nat.Prime 54977560373 := by
  apply lucas_primality 54977560373 (2 : ZMod 54977560373)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (280497757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (280497757, 1)] : List FactorBlock).map factorBlockValue).prod) = 54977560373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_280497757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54977560373) ^ 27488780186 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 54977560373) ^ 7853937196 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 54977560373) ^ 196 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_55397017171 : Nat.Prime 55397017171 := by
  apply lucas_primality 55397017171 (3 : ZMod 55397017171)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (113, 1), (307, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (113, 1), (307, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) = 55397017171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_113
      · exact prime_t64_307
      · exact prime_thirtyFiveAG_1613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55397017171) ^ 27698508585 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 18465672390 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 11079403434 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 5036092470 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 490239090 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 180446310 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55397017171) ^ 34344090 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_61286710469 : Nat.Prime 61286710469 := by
  apply lucas_primality 61286710469 (2 : ZMod 61286710469)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13099, 1), (1169683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13099, 1), (1169683, 1)] : List FactorBlock).map factorBlockValue).prod) = 61286710469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_13099
      · exact prime_thirtyFiveAG_1169683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61286710469) ^ 30643355234 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61286710469) ^ 4678732 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61286710469) ^ 52396 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_73
      · exact prime_thirtyFiveAG_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_87403578583 : Nat.Prime 87403578583 := by
  apply lucas_primality 87403578583 (3 : ZMod 87403578583)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14567263097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14567263097, 1)] : List FactorBlock).map factorBlockValue).prod) = 87403578583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_14567263097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 87403578583) ^ 43701789291 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 87403578583) ^ 29134526194 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 87403578583) ^ 6 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_116437221773 : Nat.Prime 116437221773 := by
  apply lucas_primality 116437221773 (2 : ZMod 116437221773)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (939009853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (939009853, 1)] : List FactorBlock).map factorBlockValue).prod) = 116437221773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_thirtyFiveAG_939009853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116437221773) ^ 58218610886 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116437221773) ^ 3756039412 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 116437221773) ^ 124 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_439
      · exact prime_thirtyFiveAG_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_136330035181 : Nat.Prime 136330035181 := by
  apply lucas_primality 136330035181 (11 : ZMod 136330035181)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (139, 1), (16346527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (139, 1), (16346527, 1)] : List FactorBlock).map factorBlockValue).prod) = 136330035181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_139
      · exact prime_thirtyFiveAG_16346527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 136330035181) ^ 68165017590 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 136330035181) ^ 45443345060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 136330035181) ^ 27266007036 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 136330035181) ^ 980791620 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 136330035181) ^ 8340 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_198976128383 : Nat.Prime 198976128383 := by
  apply lucas_primality 198976128383 (5 : ZMod 198976128383)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (139, 1), (223, 1), (78283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (139, 1), (223, 1), (78283, 1)] : List FactorBlock).map factorBlockValue).prod) = 198976128383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_139
      · exact prime_t64_223
      · exact prime_thirtyFiveAG_78283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 198976128383) ^ 99488064191 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 198976128383) ^ 4853076302 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 198976128383) ^ 1431482938 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 198976128383) ^ 892269634 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 198976128383) ^ 2541754 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_218249193941 : Nat.Prime 218249193941 := by
  apply lucas_primality 218249193941 (2 : ZMod 218249193941)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (10912459697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (10912459697, 1)] : List FactorBlock).map factorBlockValue).prod) = 218249193941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_10912459697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 218249193941) ^ 109124596970 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 218249193941) ^ 43649838788 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 218249193941) ^ 20 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_234156128057 : Nat.Prime 234156128057 := by
  apply lucas_primality 234156128057 (3 : ZMod 234156128057)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (552255019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (552255019, 1)] : List FactorBlock).map factorBlockValue).prod) = 234156128057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_552255019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 234156128057) ^ 117078064028 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 234156128057) ^ 4418040152 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 234156128057) ^ 424 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_239256433531 : Nat.Prime 239256433531 := by
  apply lucas_primality 239256433531 (3 : ZMod 239256433531)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (19, 1), (15546227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (19, 1), (15546227, 1)] : List FactorBlock).map factorBlockValue).prod) = 239256433531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_15546227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239256433531) ^ 119628216765 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 239256433531) ^ 79752144510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 239256433531) ^ 47851286706 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 239256433531) ^ 12592443870 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 239256433531) ^ 15390 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_305494158833 : Nat.Prime 305494158833 := by
  apply lucas_primality 305494158833 (3 : ZMod 305494158833)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (149, 1), (619, 1), (207017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (149, 1), (619, 1), (207017, 1)] : List FactorBlock).map factorBlockValue).prod) = 305494158833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_149
      · exact prime_thirtyFiveAG_619
      · exact prime_thirtyFiveAG_207017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 305494158833) ^ 152747079416 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 305494158833) ^ 2050296368 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 305494158833) ^ 493528528 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 305494158833) ^ 1475696 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_311323711037 : Nat.Prime 311323711037 := by
  apply lucas_primality 311323711037 (2 : ZMod 311323711037)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (31, 2), (647, 1), (9629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (31, 2), (647, 1), (9629, 1)] : List FactorBlock).map factorBlockValue).prod) = 311323711037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_t64_647
      · exact prime_thirtyFiveAG_9629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 311323711037) ^ 155661855518 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311323711037) ^ 23947977772 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311323711037) ^ 10042700356 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311323711037) ^ 481180388 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 311323711037) ^ 32331884 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_323190492101 : Nat.Prime 323190492101 := by
  apply lucas_primality 323190492101 (3 : ZMod 323190492101)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (19, 1), (281, 1), (86477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (19, 1), (281, 1), (86477, 1)] : List FactorBlock).map factorBlockValue).prod) = 323190492101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_281
      · exact prime_thirtyFiveAG_86477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 323190492101) ^ 161595246050 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 323190492101) ^ 64638098420 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 323190492101) ^ 46170070300 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 323190492101) ^ 17010025900 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 323190492101) ^ 1150144100 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 323190492101) ^ 3737300 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_339570147913 : Nat.Prime 339570147913 := by
  apply lucas_primality 339570147913 (7 : ZMod 339570147913)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (43, 1), (17317939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (43, 1), (17317939, 1)] : List FactorBlock).map factorBlockValue).prod) = 339570147913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_43
      · exact prime_thirtyFiveAG_17317939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 339570147913) ^ 169785073956 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 339570147913) ^ 113190049304 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 339570147913) ^ 17872113048 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 339570147913) ^ 7896980184 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 339570147913) ^ 19608 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_348527716301 : Nat.Prime 348527716301 := by
  apply lucas_primality 348527716301 (2 : ZMod 348527716301)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (3485277163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (3485277163, 1)] : List FactorBlock).map factorBlockValue).prod) = 348527716301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_3485277163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 348527716301) ^ 174263858150 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 348527716301) ^ 69705543260 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 348527716301) ^ 100 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_349676416139 : Nat.Prime 349676416139 := by
  apply lucas_primality 349676416139 (2 : ZMod 349676416139)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (1314572993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (1314572993, 1)] : List FactorBlock).map factorBlockValue).prod) = 349676416139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_1314572993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 349676416139) ^ 174838208069 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 349676416139) ^ 49953773734 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 349676416139) ^ 18404021902 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 349676416139) ^ 266 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_575998669513 : Nat.Prime 575998669513 := by
  apply lucas_primality 575998669513 (10 : ZMod 575998669513)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (19, 1), (863, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (19, 1), (863, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) = 575998669513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_863
      · exact prime_thirtyFiveAG_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 575998669513) ^ 287999334756 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 575998669513) ^ 191999556504 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 575998669513) ^ 82285524216 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 575998669513) ^ 30315719448 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 575998669513) ^ 667437624 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 575998669513) ^ 173545848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_699352832279 : Nat.Prime 699352832279 := by
  apply lucas_primality 699352832279 (23 : ZMod 699352832279)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349676416139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349676416139, 1)] : List FactorBlock).map factorBlockValue).prod) = 699352832279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_349676416139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (23 : ZMod 699352832279) ^ 349676416139 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (23 : ZMod 699352832279) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_936426298751 : Nat.Prime 936426298751 := by
  apply lucas_primality 936426298751 (11 : ZMod 936426298751)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (617, 1), (1214167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (617, 1), (1214167, 1)] : List FactorBlock).map factorBlockValue).prod) = 936426298751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_617
      · exact prime_thirtyFiveAG_1214167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 936426298751) ^ 468213149375 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 936426298751) ^ 187285259750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 936426298751) ^ 1517708750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 936426298751) ^ 771250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_985016820817 : Nat.Prime 985016820817 := by
  apply lucas_primality 985016820817 (5 : ZMod 985016820817)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (5639, 1), (173293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (5639, 1), (173293, 1)] : List FactorBlock).map factorBlockValue).prod) = 985016820817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_5639
      · exact prime_thirtyFiveAG_173293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 985016820817) ^ 492508410408 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 985016820817) ^ 328338940272 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 985016820817) ^ 140716688688 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 985016820817) ^ 174679344 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 985016820817) ^ 5684112 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1090772513377 : Nat.Prime 1090772513377 := by
  apply lucas_primality 1090772513377 (5 : ZMod 1090772513377)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (13, 1), (10313, 1), (12107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (13, 1), (10313, 1), (12107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090772513377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_10313
      · exact prime_thirtyFiveAG_12107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1090772513377) ^ 545386256688 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090772513377) ^ 363590837792 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090772513377) ^ 155824644768 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090772513377) ^ 83905577952 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090772513377) ^ 105766752 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1090772513377) ^ 90094368 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1312200053707 : Nat.Prime 1312200053707 := by
  apply lucas_primality 1312200053707 (2 : ZMod 1312200053707)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (7541379619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (7541379619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1312200053707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_thirtyFiveAG_7541379619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1312200053707) ^ 656100026853 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312200053707) ^ 437400017902 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312200053707) ^ 45248277714 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1312200053707) ^ 174 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1355595084643 : Nat.Prime 1355595084643 := by
  apply lucas_primality 1355595084643 (3 : ZMod 1355595084643)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (263, 1), (45213631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (263, 1), (45213631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1355595084643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_263
      · exact prime_thirtyFiveAG_45213631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1355595084643) ^ 677797542321 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1355595084643) ^ 451865028214 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1355595084643) ^ 71347109718 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1355595084643) ^ 5154353934 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1355595084643) ^ 29982 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_397
      · exact prime_thirtyFiveAG_977
      · exact prime_thirtyFiveAG_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1530731964673 : Nat.Prime 1530731964673 := by
  apply lucas_primality 1530731964673 (5 : ZMod 1530731964673)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (2657, 1), (250049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (2657, 1), (250049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530731964673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_2657
      · exact prime_thirtyFiveAG_250049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1530731964673) ^ 765365982336 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530731964673) ^ 510243988224 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530731964673) ^ 576112896 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530731964673) ^ 6121728 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1674224493737 : Nat.Prime 1674224493737 := by
  apply lucas_primality 1674224493737 (3 : ZMod 1674224493737)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (101, 1), (449, 1), (75653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (101, 1), (449, 1), (75653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674224493737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_t64_101
      · exact prime_thirtyFiveAG_449
      · exact prime_thirtyFiveAG_75653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1674224493737) ^ 837112246868 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1674224493737) ^ 27446303176 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1674224493737) ^ 16576480136 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1674224493737) ^ 3728785064 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1674224493737) ^ 22130312 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2096733381217 : Nat.Prime 2096733381217 := by
  apply lucas_primality 2096733381217 (5 : ZMod 2096733381217)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2909, 1), (7508069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2909, 1), (7508069, 1)] : List FactorBlock).map factorBlockValue).prod) = 2096733381217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_2909
      · exact prime_thirtyFiveAG_7508069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2096733381217) ^ 1048366690608 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2096733381217) ^ 698911127072 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2096733381217) ^ 720774624 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2096733381217) ^ 279264 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2528433666191 : Nat.Prime 2528433666191 := by
  apply lucas_primality 2528433666191 (11 : ZMod 2528433666191)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (6037, 1), (1820969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (6037, 1), (1820969, 1)] : List FactorBlock).map factorBlockValue).prod) = 2528433666191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_6037
      · exact prime_thirtyFiveAG_1820969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2528433666191) ^ 1264216833095 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2528433666191) ^ 505686733238 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2528433666191) ^ 109931898530 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2528433666191) ^ 418822870 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2528433666191) ^ 1388510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2789696488343 : Nat.Prime 2789696488343 := by
  apply lucas_primality 2789696488343 (5 : ZMod 2789696488343)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8681, 1), (11411, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8681, 1), (11411, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) = 2789696488343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_8681
      · exact prime_thirtyFiveAG_11411
      · exact prime_thirtyFiveAG_14081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2789696488343) ^ 1394848244171 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2789696488343) ^ 321356582 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2789696488343) ^ 244474322 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2789696488343) ^ 198117782 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3233670084961 : Nat.Prime 3233670084961 := by
  apply lucas_primality 3233670084961 (11 : ZMod 3233670084961)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 2), (23, 1), (5977651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 2), (23, 1), (5977651, 1)] : List FactorBlock).map factorBlockValue).prod) = 3233670084961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_5977651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3233670084961) ^ 1616835042480 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3233670084961) ^ 1077890028320 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3233670084961) ^ 646734016992 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3233670084961) ^ 461952869280 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3233670084961) ^ 140594351520 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3233670084961) ^ 540960 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5056867332383 : Nat.Prime 5056867332383 := by
  apply lucas_primality 5056867332383 (5 : ZMod 5056867332383)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2528433666191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2528433666191, 1)] : List FactorBlock).map factorBlockValue).prod) = 5056867332383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_2528433666191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5056867332383) ^ 2528433666191 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5056867332383) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5086467135259 : Nat.Prime 5086467135259 := by
  apply lucas_primality 5086467135259 (10 : ZMod 5086467135259)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11617, 1), (72974479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11617, 1), (72974479, 1)] : List FactorBlock).map factorBlockValue).prod) = 5086467135259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_11617
      · exact prime_thirtyFiveAG_72974479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5086467135259) ^ 2543233567629 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 5086467135259) ^ 1695489045086 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 5086467135259) ^ 437846874 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 5086467135259) ^ 69702 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_381559
      · exact prime_thirtyFiveAG_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5639337539207 : Nat.Prime 5639337539207 := by
  apply lucas_primality 5639337539207 (5 : ZMod 5639337539207)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (199, 1), (733, 1), (1327, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (199, 1), (733, 1), (1327, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 5639337539207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_199
      · exact prime_thirtyFiveAG_733
      · exact prime_thirtyFiveAG_1327
      · exact prime_thirtyFiveAG_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5639337539207) ^ 2819668769603 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639337539207) ^ 805619648458 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639337539207) ^ 28338379594 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639337539207) ^ 7693502782 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639337539207) ^ 4249689178 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5639337539207) ^ 2709917126 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_9829044374857 : Nat.Prime 9829044374857 := by
  apply lucas_primality 9829044374857 (10 : ZMod 9829044374857)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (31, 1), (211, 1), (1277791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (31, 1), (211, 1), (1277791, 1)] : List FactorBlock).map factorBlockValue).prod) = 9829044374857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_thirtyFiveAG_211
      · exact prime_thirtyFiveAG_1277791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9829044374857) ^ 4914522187428 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 9829044374857) ^ 3276348124952 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 9829044374857) ^ 1404149196408 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 9829044374857) ^ 317065947576 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 9829044374857) ^ 46583148696 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 9829044374857) ^ 7692216 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_10032152737987 : Nat.Prime 10032152737987 := by
  apply lucas_primality 10032152737987 (2 : ZMod 10032152737987)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (41, 1), (1510411433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (41, 1), (1510411433, 1)] : List FactorBlock).map factorBlockValue).prod) = 10032152737987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_1510411433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10032152737987) ^ 5016076368993 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10032152737987) ^ 3344050912662 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10032152737987) ^ 244686652146 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10032152737987) ^ 6642 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_10113734664767 : Nat.Prime 10113734664767 := by
  apply lucas_primality 10113734664767 (5 : ZMod 10113734664767)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5056867332383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5056867332383, 1)] : List FactorBlock).map factorBlockValue).prod) = 10113734664767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_5056867332383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10113734664767) ^ 5056867332383 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 10113734664767) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_thirtyFiveAG_971
      · exact prime_thirtyFiveAG_1031
      · exact prime_thirtyFiveAG_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_13344423692081 : Nat.Prime 13344423692081 := by
  apply lucas_primality 13344423692081 (3 : ZMod 13344423692081)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (12831176627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (12831176627, 1)] : List FactorBlock).map factorBlockValue).prod) = 13344423692081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_12831176627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13344423692081) ^ 6672211846040 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13344423692081) ^ 2668884738416 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13344423692081) ^ 1026494130160 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13344423692081) ^ 1040 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_14314091514911 : Nat.Prime 14314091514911 := by
  apply lucas_primality 14314091514911 (11 : ZMod 14314091514911)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (541, 1), (1297, 1), (10909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (541, 1), (1297, 1), (10909, 1)] : List FactorBlock).map factorBlockValue).prod) = 14314091514911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_thirtyFiveAG_541
      · exact prime_thirtyFiveAG_1297
      · exact prime_thirtyFiveAG_10909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14314091514911) ^ 7157045757455 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 2862818302982 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 1301281046810 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 842005383230 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 26458579510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 11036308030 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 14314091514911) ^ 1312135990 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_21905722901677 : Nat.Prime 21905722901677 := by
  apply lucas_primality 21905722901677 (2 : ZMod 21905722901677)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (350351, 1), (5210423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (350351, 1), (5210423, 1)] : List FactorBlock).map factorBlockValue).prod) = 21905722901677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_350351
      · exact prime_thirtyFiveAG_5210423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21905722901677) ^ 10952861450838 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21905722901677) ^ 7301907633892 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21905722901677) ^ 62525076 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21905722901677) ^ 4204212 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_t64_97
      · exact prime_thirtyFiveAG_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_22379290632929 : Nat.Prime 22379290632929 := by
  apply lucas_primality 22379290632929 (3 : ZMod 22379290632929)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (699352832279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (699352832279, 1)] : List FactorBlock).map factorBlockValue).prod) = 22379290632929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_699352832279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22379290632929) ^ 11189645316464 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 22379290632929) ^ 32 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_25869183698957 : Nat.Prime 25869183698957 := by
  apply lucas_primality 25869183698957 (2 : ZMod 25869183698957)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (16693, 1), (29801971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (16693, 1), (29801971, 1)] : List FactorBlock).map factorBlockValue).prod) = 25869183698957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_16693
      · exact prime_thirtyFiveAG_29801971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25869183698957) ^ 12934591849478 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25869183698957) ^ 1989937207612 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25869183698957) ^ 1549702492 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25869183698957) ^ 868036 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_38072781057037 : Nat.Prime 38072781057037 := by
  apply lucas_primality 38072781057037 (5 : ZMod 38072781057037)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (71, 1), (3109, 1), (118787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (71, 1), (3109, 1), (118787, 1)] : List FactorBlock).map factorBlockValue).prod) = 38072781057037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_71
      · exact prime_thirtyFiveAG_3109
      · exact prime_thirtyFiveAG_118787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38072781057037) ^ 19036390528518 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38072781057037) ^ 12690927019012 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38072781057037) ^ 3461161914276 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38072781057037) ^ 536236352916 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38072781057037) ^ 12245989404 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 38072781057037) ^ 320513028 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_thirtyFiveAG_293
      · exact prime_t64_317
      · exact prime_thirtyFiveAG_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_101
      · exact prime_thirtyFiveAG_5779
      · exact prime_thirtyFiveAG_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_601
      · exact prime_thirtyFiveAG_1069
      · exact prime_thirtyFiveAG_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_56029235811859 : Nat.Prime 56029235811859 := by
  apply lucas_primality 56029235811859 (2 : ZMod 56029235811859)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (9397, 1), (11422337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (9397, 1), (11422337, 1)] : List FactorBlock).map factorBlockValue).prod) = 56029235811859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_thirtyFiveAG_9397
      · exact prime_thirtyFiveAG_11422337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56029235811859) ^ 28014617905929 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56029235811859) ^ 18676411937286 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56029235811859) ^ 1932042614202 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56029235811859) ^ 5962459914 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 56029235811859) ^ 4905234 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_56030347123169 : Nat.Prime 56030347123169 := by
  apply lucas_primality 56030347123169 (3 : ZMod 56030347123169)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (967, 1), (2917, 1), (56431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (967, 1), (2917, 1), (56431, 1)] : List FactorBlock).map factorBlockValue).prod) = 56030347123169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_967
      · exact prime_thirtyFiveAG_2917
      · exact prime_thirtyFiveAG_56431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56030347123169) ^ 28015173561584 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56030347123169) ^ 5093667920288 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56030347123169) ^ 57942447904 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56030347123169) ^ 19208209504 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 56030347123169) ^ 992900128 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_76561173554743 : Nat.Prime 76561173554743 := by
  apply lucas_primality 76561173554743 (3 : ZMod 76561173554743)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (113, 1), (229, 1), (1499, 1), (36551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (113, 1), (229, 1), (1499, 1), (36551, 1)] : List FactorBlock).map factorBlockValue).prod) = 76561173554743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_113
      · exact prime_t64_229
      · exact prime_thirtyFiveAG_1499
      · exact prime_thirtyFiveAG_36551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 76561173554743) ^ 38280586777371 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 76561173554743) ^ 25520391184914 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 76561173554743) ^ 677532509334 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 76561173554743) ^ 334328268798 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 76561173554743) ^ 51074832258 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 76561173554743) ^ 2094639642 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_103819687534487 : Nat.Prime 103819687534487 := by
  apply lucas_primality 103819687534487 (5 : ZMod 103819687534487)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (61286710469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (61286710469, 1)] : List FactorBlock).map factorBlockValue).prod) = 103819687534487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_61286710469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 103819687534487) ^ 51909843767243 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103819687534487) ^ 14831383933498 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103819687534487) ^ 9438153412226 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 103819687534487) ^ 1694 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_119674904412433 : Nat.Prime 119674904412433 := by
  apply lucas_primality 119674904412433 (5 : ZMod 119674904412433)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (29, 1), (829, 1), (4509013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (29, 1), (829, 1), (4509013, 1)] : List FactorBlock).map factorBlockValue).prod) = 119674904412433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_thirtyFiveAG_829
      · exact prime_thirtyFiveAG_4509013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 119674904412433) ^ 59837452206216 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119674904412433) ^ 39891634804144 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119674904412433) ^ 5203256713584 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119674904412433) ^ 4126720841808 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119674904412433) ^ 144360560208 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 119674904412433) ^ 26541264 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_136542857203531 : Nat.Prime 136542857203531 := by
  apply lucas_primality 136542857203531 (3 : ZMod 136542857203531)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (41, 1), (67, 1), (8699, 1), (21163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (41, 1), (67, 1), (8699, 1), (21163, 1)] : List FactorBlock).map factorBlockValue).prod) = 136542857203531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_t64_67
      · exact prime_thirtyFiveAG_8699
      · exact prime_thirtyFiveAG_21163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 136542857203531) ^ 68271428601765 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 45514285734510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 27308571440706 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 3330313590330 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 2037953092590 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 15696385470 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 136542857203531) ^ 6451961310 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_257792009005423 : Nat.Prime 257792009005423 := by
  apply lucas_primality 257792009005423 (5 : ZMod 257792009005423)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (116437221773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (116437221773, 1)] : List FactorBlock).map factorBlockValue).prod) = 257792009005423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_116437221773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 257792009005423) ^ 128896004502711 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 257792009005423) ^ 85930669668474 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 257792009005423) ^ 6287609975742 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 257792009005423) ^ 2214 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_283615046165023 : Nat.Prime 283615046165023 := by
  apply lucas_primality 283615046165023 (3 : ZMod 283615046165023)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_1163
      · exact prime_thirtyFiveAG_1663
      · exact prime_thirtyFiveAG_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283615046165023) ^ 141807523082511 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 94538348721674 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 25783186015002 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21816542012694 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 243865043994 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 170544224994 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 283615046165023) ^ 21572605626 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_364286161507483 : Nat.Prime 364286161507483 := by
  apply lucas_primality 364286161507483 (2 : ZMod 364286161507483)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2026751, 1), (9985499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2026751, 1), (9985499, 1)] : List FactorBlock).map factorBlockValue).prod) = 364286161507483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_2026751
      · exact prime_thirtyFiveAG_9985499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 364286161507483) ^ 182143080753741 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364286161507483) ^ 121428720502494 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364286161507483) ^ 179738982 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364286161507483) ^ 36481518 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_385798942143929 : Nat.Prime 385798942143929 := by
  apply lucas_primality 385798942143929 (3 : ZMod 385798942143929)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (2096733381217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (2096733381217, 1)] : List FactorBlock).map factorBlockValue).prod) = 385798942143929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_2096733381217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 385798942143929) ^ 192899471071964 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 385798942143929) ^ 16773867049736 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 385798942143929) ^ 184 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_437528854855949 : Nat.Prime 437528854855949 := by
  apply lucas_primality 437528854855949 (2 : ZMod 437528854855949)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2459, 1), (44482396793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2459, 1), (44482396793, 1)] : List FactorBlock).map factorBlockValue).prod) = 437528854855949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_2459
      · exact prime_thirtyFiveAG_44482396793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 437528854855949) ^ 218764427427974 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 437528854855949) ^ 177929587172 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 437528854855949) ^ 9836 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_442209577989539 : Nat.Prime 442209577989539 := by
  apply lucas_primality 442209577989539 (2 : ZMod 442209577989539)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (415153, 1), (1965263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (415153, 1), (1965263, 1)] : List FactorBlock).map factorBlockValue).prod) = 442209577989539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_271
      · exact prime_thirtyFiveAG_415153
      · exact prime_thirtyFiveAG_1965263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 442209577989539) ^ 221104788994769 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 442209577989539) ^ 1631769660478 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 442209577989539) ^ 1065172546 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 442209577989539) ^ 225012926 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_t64_233
      · exact prime_t64_409
      · exact prime_thirtyFiveAG_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_629058839990849 : Nat.Prime 629058839990849 := by
  apply lucas_primality 629058839990849 (3 : ZMod 629058839990849)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (9829044374857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (9829044374857, 1)] : List FactorBlock).map factorBlockValue).prod) = 629058839990849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_9829044374857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 629058839990849) ^ 314529419995424 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 629058839990849) ^ 64 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_223
      · exact prime_t64_283
      · exact prime_thirtyFiveAG_5843
      · exact prime_thirtyFiveAG_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_961332349927559 : Nat.Prime 961332349927559 := by
  apply lucas_primality 961332349927559 (7 : ZMod 961332349927559)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (41, 1), (239256433531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (41, 1), (239256433531, 1)] : List FactorBlock).map factorBlockValue).prod) = 961332349927559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_239256433531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 961332349927559) ^ 480666174963779 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 961332349927559) ^ 137333192846794 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 961332349927559) ^ 23447130486038 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 961332349927559) ^ 4018 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1653892391684899 : Nat.Prime 1653892391684899 := by
  apply lucas_primality 1653892391684899 (7 : ZMod 1653892391684899)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (421, 1), (218249193941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (421, 1), (218249193941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1653892391684899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_421
      · exact prime_thirtyFiveAG_218249193941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1653892391684899) ^ 826946195842449 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1653892391684899) ^ 551297463894966 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1653892391684899) ^ 3928485490938 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1653892391684899) ^ 7578 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1998641547176479 : Nat.Prime 1998641547176479 := by
  apply lucas_primality 1998641547176479 (3 : ZMod 1998641547176479)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9211919, 1), (36160427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9211919, 1), (36160427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1998641547176479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_9211919
      · exact prime_thirtyFiveAG_36160427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1998641547176479) ^ 999320773588239 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1998641547176479) ^ 666213849058826 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1998641547176479) ^ 216962562 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1998641547176479) ^ 55271514 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2131413249403297 : Nat.Prime 2131413249403297 := by
  apply lucas_primality 2131413249403297 (5 : ZMod 2131413249403297)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (6577, 1), (1125245621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (6577, 1), (1125245621, 1)] : List FactorBlock).map factorBlockValue).prod) = 2131413249403297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_6577
      · exact prime_thirtyFiveAG_1125245621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2131413249403297) ^ 1065706624701648 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2131413249403297) ^ 710471083134432 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2131413249403297) ^ 324070738848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2131413249403297) ^ 1894176 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2184685715256497 : Nat.Prime 2184685715256497 := by
  apply lucas_primality 2184685715256497 (3 : ZMod 2184685715256497)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (136542857203531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (136542857203531, 1)] : List FactorBlock).map factorBlockValue).prod) = 2184685715256497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_136542857203531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2184685715256497) ^ 1092342857628248 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2184685715256497) ^ 16 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2655012492576541 : Nat.Prime 2655012492576541 := by
  apply lucas_primality 2655012492576541 (2 : ZMod 2655012492576541)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (613, 1), (1153, 1), (20869127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (613, 1), (1153, 1), (20869127, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655012492576541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_613
      · exact prime_t64_1153
      · exact prime_thirtyFiveAG_20869127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2655012492576541) ^ 1327506246288270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655012492576541) ^ 885004164192180 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655012492576541) ^ 531002498515308 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655012492576541) ^ 4331178617580 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655012492576541) ^ 2302699473180 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655012492576541) ^ 127222020 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_3945148126310507 : Nat.Prime 3945148126310507 := by
  apply lucas_primality 3945148126310507 (2 : ZMod 3945148126310507)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (103819687534487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (103819687534487, 1)] : List FactorBlock).map factorBlockValue).prod) = 3945148126310507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_thirtyFiveAG_103819687534487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3945148126310507) ^ 1972574063155253 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3945148126310507) ^ 207639375068974 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3945148126310507) ^ 38 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_4243526734081759 : Nat.Prime 4243526734081759 := by
  apply lucas_primality 4243526734081759 (3 : ZMod 4243526734081759)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (13344423692081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (13344423692081, 1)] : List FactorBlock).map factorBlockValue).prod) = 4243526734081759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_13344423692081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4243526734081759) ^ 2121763367040879 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243526734081759) ^ 1414508911360586 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243526734081759) ^ 80066542152486 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4243526734081759) ^ 318 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_12135287197724137 : Nat.Prime 12135287197724137 := by
  apply lucas_primality 12135287197724137 (5 : ZMod 12135287197724137)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (373, 1), (1355595084643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (373, 1), (1355595084643, 1)] : List FactorBlock).map factorBlockValue).prod) = 12135287197724137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_373
      · exact prime_thirtyFiveAG_1355595084643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12135287197724137) ^ 6067643598862068 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 12135287197724137) ^ 4045095732574712 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 12135287197724137) ^ 32534282031432 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 12135287197724137) ^ 8952 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_12398369604474701 : Nat.Prime 12398369604474701 := by
  apply lucas_primality 12398369604474701 (2 : ZMod 12398369604474701)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_247757789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12398369604474701) ^ 6199184802237350 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 2479673920894940 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1771195657782100 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 1127124509497700 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 185050292604100 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 127818243345100 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12398369604474701) ^ 50042300 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_t64_163
      · exact prime_thirtyFiveAG_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_656951
      · exact prime_thirtyFiveAG_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_58438367615106233 : Nat.Prime 58438367615106233 := by
  apply lucas_primality 58438367615106233 (3 : ZMod 58438367615106233)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (15349, 1), (36608728967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (15349, 1), (36608728967, 1)] : List FactorBlock).map factorBlockValue).prod) = 58438367615106233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_15349
      · exact prime_thirtyFiveAG_36608728967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58438367615106233) ^ 29219183807553116 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58438367615106233) ^ 4495259047315864 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58438367615106233) ^ 3807307812568 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58438367615106233) ^ 1596296 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_86944695168309299 : Nat.Prime 86944695168309299 := by
  apply lucas_primality 86944695168309299 (2 : ZMod 86944695168309299)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1063, 1), (575998669513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1063, 1), (575998669513, 1)] : List FactorBlock).map factorBlockValue).prod) = 86944695168309299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_71
      · exact prime_thirtyFiveAG_1063
      · exact prime_thirtyFiveAG_575998669513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 86944695168309299) ^ 43472347584154649 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 86944695168309299) ^ 1224573171384638 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 86944695168309299) ^ 81791811070846 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 86944695168309299) ^ 150946 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_97937826197793863 : Nat.Prime 97937826197793863 := by
  apply lucas_primality 97937826197793863 (5 : ZMod 97937826197793863)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) = 97937826197793863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_t64_167
      · exact prime_thirtyFiveAG_316097
      · exact prime_thirtyFiveAG_1489003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97937826197793863) ^ 48968913098896931 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 13991118028256266 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 1100425013458358 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 586454049088586 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 309834722246 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 65774095954 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_114218290024018991 : Nat.Prime 114218290024018991 := by
  apply lucas_primality 114218290024018991 (17 : ZMod 114218290024018991)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) = 114218290024018991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_491
      · exact prime_thirtyFiveAG_2677
      · exact prime_thirtyFiveAG_15073
      · exact prime_thirtyFiveAG_576509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 114218290024018991) ^ 57109145012009495 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 22843658004803798 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 232623808602890 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 42666525970870 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 7577674651630 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 198120567110 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_79
      · exact prime_thirtyFiveAG_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_244099687050225529 : Nat.Prime 244099687050225529 := by
  apply lucas_primality 244099687050225529 (7 : ZMod 244099687050225529)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (442209577989539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (442209577989539, 1)] : List FactorBlock).map factorBlockValue).prod) = 244099687050225529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_thirtyFiveAG_442209577989539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 244099687050225529) ^ 122049843525112764 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 244099687050225529) ^ 81366562350075176 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 244099687050225529) ^ 10613029871748936 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 244099687050225529) ^ 552 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_252645265925168009 : Nat.Prime 252645265925168009 := by
  apply lucas_primality 252645265925168009 (3 : ZMod 252645265925168009)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      · exact prime_thirtyFiveAG_13421
      · exact prime_thirtyFiveAG_99611
      · exact prime_thirtyFiveAG_23622671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252645265925168009) ^ 126322632962584004 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 18824623047848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 2536318939928 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 252645265925168009) ^ 10695033848 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_451009125414846629 : Nat.Prime 451009125414846629 := by
  apply lucas_primality 451009125414846629 (2 : ZMod 451009125414846629)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (103, 1), (167, 1), (936426298751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (103, 1), (167, 1), (936426298751, 1)] : List FactorBlock).map factorBlockValue).prod) = 451009125414846629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_103
      · exact prime_t64_167
      · exact prime_thirtyFiveAG_936426298751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 451009125414846629) ^ 225504562707423314 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 451009125414846629) ^ 64429875059263804 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 451009125414846629) ^ 4378729372959676 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 451009125414846629) ^ 2700653445597884 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 451009125414846629) ^ 481628 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_528064289915195393 : Nat.Prime 528064289915195393 := by
  apply lucas_primality 528064289915195393 (3 : ZMod 528064289915195393)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (11719, 1), (11001104683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (11719, 1), (11001104683, 1)] : List FactorBlock).map factorBlockValue).prod) = 528064289915195393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_11719
      · exact prime_thirtyFiveAG_11001104683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 528064289915195393) ^ 264032144957597696 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 528064289915195393) ^ 45060524781568 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 528064289915195393) ^ 48001024 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1867578469061212741 : Nat.Prime 1867578469061212741 := by
  apply lucas_primality 1867578469061212741 (2 : ZMod 1867578469061212741)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (443, 1), (479, 1), (20955128501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (443, 1), (479, 1), (20955128501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1867578469061212741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_443
      · exact prime_t64_479
      · exact prime_thirtyFiveAG_20955128501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1867578469061212741) ^ 933789234530606370 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 622526156353737580 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 373515693812242548 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 266796924151601820 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 4215752751831180 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 3898911208896060 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1867578469061212741) ^ 89122740 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2256209600582983583 : Nat.Prime 2256209600582983583 := by
  apply lucas_primality 2256209600582983583 (5 : ZMod 2256209600582983583)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (23608747, 1), (1165447333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (23608747, 1), (1165447333, 1)] : List FactorBlock).map factorBlockValue).prod) = 2256209600582983583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_thirtyFiveAG_23608747
      · exact prime_thirtyFiveAG_1165447333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2256209600582983583) ^ 1128104800291491791 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2256209600582983583) ^ 55029502453243502 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2256209600582983583) ^ 95566681306 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2256209600582983583) ^ 1935917254 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_4956087853639023553 : Nat.Prime 4956087853639023553 := by
  apply lucas_primality 4956087853639023553 (5 : ZMod 4956087853639023553)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (23, 1), (53, 1), (3253, 1), (197258651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (23, 1), (53, 1), (3253, 1), (197258651, 1)] : List FactorBlock).map factorBlockValue).prod) = 4956087853639023553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_t64_53
      · exact prime_thirtyFiveAG_3253
      · exact prime_thirtyFiveAG_197258651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4956087853639023553) ^ 2478043926819511776 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 1652029284546341184 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 450553441239911232 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 215482080593001024 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 93511091578094784 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 1523543760725184 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4956087853639023553) ^ 25124818752 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_12796887190183641869 : Nat.Prime 12796887190183641869 := by
  apply lucas_primality 12796887190183641869 (2 : ZMod 12796887190183641869)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (989347, 1), (3233670084961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (989347, 1), (3233670084961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12796887190183641869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_989347
      · exact prime_thirtyFiveAG_3233670084961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12796887190183641869) ^ 6398443595091820934 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12796887190183641869) ^ 12934680339844 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12796887190183641869) ^ 3957388 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_39082881220893000391 : Nat.Prime 39082881220893000391 := by
  apply lucas_primality 39082881220893000391 (6 : ZMod 39082881220893000391)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (307, 1), (4243526734081759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (307, 1), (4243526734081759, 1)] : List FactorBlock).map factorBlockValue).prod) = 39082881220893000391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_307
      · exact prime_thirtyFiveAG_4243526734081759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39082881220893000391) ^ 19541440610446500195 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 39082881220893000391) ^ 13027627073631000130 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 39082881220893000391) ^ 7816576244178600078 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 39082881220893000391) ^ 127305802022452770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 39082881220893000391) ^ 9210 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_92741394945401364329 : Nat.Prime 92741394945401364329 := by
  apply lucas_primality 92741394945401364329 (3 : ZMod 92741394945401364329)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (453090653, 1), (1505045441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (453090653, 1), (1505045441, 1)] : List FactorBlock).map factorBlockValue).prod) = 92741394945401364329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_thirtyFiveAG_453090653
      · exact prime_thirtyFiveAG_1505045441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 92741394945401364329) ^ 46370697472700682164 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 92741394945401364329) ^ 5455376173258903784 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 92741394945401364329) ^ 204686179976 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 92741394945401364329) ^ 61620328808 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_139
      · exact prime_thirtyFiveAG_413869
      · exact prime_thirtyFiveAG_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_321796510933018345391 : Nat.Prime 321796510933018345391 := by
  apply lucas_primality 321796510933018345391 (13 : ZMod 321796510933018345391)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (415517, 1), (1090772513377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (415517, 1), (1090772513377, 1)] : List FactorBlock).map factorBlockValue).prod) = 321796510933018345391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_thirtyFiveAG_415517
      · exact prime_thirtyFiveAG_1090772513377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 321796510933018345391) ^ 160898255466509172695 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 321796510933018345391) ^ 64359302186603669078 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 321796510933018345391) ^ 4532345224408709090 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 321796510933018345391) ^ 774448484497670 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (13 : ZMod 321796510933018345391) ^ 295017070 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_361586454322254942197 : Nat.Prime 361586454322254942197 := by
  apply lucas_primality 361586454322254942197 (2 : ZMod 361586454322254942197)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) = 361586454322254942197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_71
      · exact prime_thirtyFiveAG_97937826197793863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361586454322254942197) ^ 180793227161127471098 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 27814342640173457092 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 5092766962285280876 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 3692 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_607348163015529886877 : Nat.Prime 607348163015529886877 := by
  apply lucas_primality 607348163015529886877 (2 : ZMod 607348163015529886877)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) = 607348163015529886877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_2837
      · exact prime_thirtyFiveAG_2633923
      · exact prime_thirtyFiveAG_20319607769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607348163015529886877) ^ 303674081507764943438 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 214081129014991148 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 230586908962612 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 29889758204 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_743645979331646056093 : Nat.Prime 743645979331646056093 := by
  apply lucas_primality 743645979331646056093 (2 : ZMod 743645979331646056093)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (7649, 1), (385798942143929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (7649, 1), (385798942143929, 1)] : List FactorBlock).map factorBlockValue).prod) = 743645979331646056093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_thirtyFiveAG_7649
      · exact prime_thirtyFiveAG_385798942143929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 743645979331646056093) ^ 371822989665823028046 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 743645979331646056093) ^ 247881993110548685364 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 743645979331646056093) ^ 106235139904520865156 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 743645979331646056093) ^ 97221333420270108 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 743645979331646056093) ^ 1927548 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_769581921098236174261 : Nat.Prime 769581921098236174261 := by
  apply lucas_primality 769581921098236174261 (6 : ZMod 769581921098236174261)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4831, 1), (2655012492576541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4831, 1), (2655012492576541, 1)] : List FactorBlock).map factorBlockValue).prod) = 769581921098236174261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_4831
      · exact prime_thirtyFiveAG_2655012492576541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 769581921098236174261) ^ 384790960549118087130 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 769581921098236174261) ^ 256527307032745391420 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 769581921098236174261) ^ 153916384219647234852 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 769581921098236174261) ^ 159300749554592460 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 769581921098236174261) ^ 289860 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1074222672606781183091 : Nat.Prime 1074222672606781183091 := by
  apply lucas_primality 1074222672606781183091 (2 : ZMod 1074222672606781183091)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (151, 1), (65657, 1), (985016820817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (151, 1), (65657, 1), (985016820817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074222672606781183091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_151
      · exact prime_thirtyFiveAG_65657
      · exact prime_thirtyFiveAG_985016820817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1074222672606781183091) ^ 537111336303390591545 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074222672606781183091) ^ 214844534521356236618 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074222672606781183091) ^ 97656606600616471190 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074222672606781183091) ^ 7114057434481994590 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074222672606781183091) ^ 16361129393770370 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074222672606781183091) ^ 1090562770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_2077599264363442635953 : Nat.Prime 2077599264363442635953 := by
  apply lucas_primality 2077599264363442635953 (3 : ZMod 2077599264363442635953)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2791, 1), (149441, 1), (311323711037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2791, 1), (149441, 1), (311323711037, 1)] : List FactorBlock).map factorBlockValue).prod) = 2077599264363442635953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_2791
      · exact prime_thirtyFiveAG_149441
      · exact prime_thirtyFiveAG_311323711037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2077599264363442635953) ^ 1038799632181721317976 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077599264363442635953) ^ 744392427217285072 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077599264363442635953) ^ 13902471640068272 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077599264363442635953) ^ 6673437296 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_29
      · exact prime_t64_431
      · exact prime_thirtyFiveAG_3532679
      · exact prime_thirtyFiveAG_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_6299123778170308210303 : Nat.Prime 6299123778170308210303 := by
  apply lucas_primality 6299123778170308210303 (3 : ZMod 6299123778170308210303)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2924183, 1), (119674904412433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2924183, 1), (119674904412433, 1)] : List FactorBlock).map factorBlockValue).prod) = 6299123778170308210303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_2924183
      · exact prime_thirtyFiveAG_119674904412433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6299123778170308210303) ^ 3149561889085154105151 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6299123778170308210303) ^ 2099707926056769403434 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6299123778170308210303) ^ 2154148279423794 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6299123778170308210303) ^ 52635294 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_67
      · exact prime_thirtyFiveAG_19379
      · exact prime_thirtyFiveAG_311677
      · exact prime_thirtyFiveAG_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_11696354891827848668267 : Nat.Prime 11696354891827848668267 := by
  apply lucas_primality 11696354891827848668267 (2 : ZMod 11696354891827848668267)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (12796887190183641869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (12796887190183641869, 1)] : List FactorBlock).map factorBlockValue).prod) = 11696354891827848668267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_457
      · exact prime_thirtyFiveAG_12796887190183641869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11696354891827848668267) ^ 5848177445913924334133 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696354891827848668267) ^ 25593774380367283738 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696354891827848668267) ^ 914 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_6475879
      · exact prime_thirtyFiveAG_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_42412987871002993312927 : Nat.Prime 42412987871002993312927 := by
  apply lucas_primality 42412987871002993312927 (6 : ZMod 42412987871002993312927)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (1193, 1), (4951, 1), (2789696488343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (1193, 1), (4951, 1), (2789696488343, 1)] : List FactorBlock).map factorBlockValue).prod) = 42412987871002993312927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_1193
      · exact prime_thirtyFiveAG_4951
      · exact prime_thirtyFiveAG_2789696488343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42412987871002993312927) ^ 21206493935501496656463 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 14137662623667664437642 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 3855726170091181210266 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 3262537528538691793302 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 35551540545685660782 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 8566549761866894226 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (6 : ZMod 42412987871002993312927) ^ 15203441682 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_69163144288181203242091 : Nat.Prime 69163144288181203242091 := by
  apply lucas_primality 69163144288181203242091 (2 : ZMod 69163144288181203242091)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (193, 1), (1499, 1), (21517, 1), (6277125343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (193, 1), (1499, 1), (21517, 1), (6277125343, 1)] : List FactorBlock).map factorBlockValue).prod) = 69163144288181203242091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_59
      · exact prime_t64_193
      · exact prime_thirtyFiveAG_1499
      · exact prime_thirtyFiveAG_21517
      · exact prime_thirtyFiveAG_6277125343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69163144288181203242091) ^ 34581572144090601621045 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 23054381429393734414030 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 13832628857636240648418 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 1172256682850528868510 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 358358260560524369130 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 46139522540481122910 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 3214348853844922770 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69163144288181203242091) ^ 11018283132630 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_69982531053084369974509 : Nat.Prime 69982531053084369974509 := by
  apply lucas_primality 69982531053084369974509 (2 : ZMod 69982531053084369974509)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (491, 1), (2753, 1), (113437, 1), (38033471159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (491, 1), (2753, 1), (113437, 1), (38033471159, 1)] : List FactorBlock).map factorBlockValue).prod) = 69982531053084369974509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_491
      · exact prime_thirtyFiveAG_2753
      · exact prime_thirtyFiveAG_113437
      · exact prime_thirtyFiveAG_38033471159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69982531053084369974509) ^ 34991265526542184987254 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69982531053084369974509) ^ 23327510351028123324836 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69982531053084369974509) ^ 142530613142738024388 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69982531053084369974509) ^ 25420461697451641836 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69982531053084369974509) ^ 616928612825483484 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 69982531053084369974509) ^ 1840024823412 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_74557236732183868791043 : Nat.Prime 74557236732183868791043 := by
  apply lucas_primality 74557236732183868791043 (3 : ZMod 74557236732183868791043)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (36264479, 1), (38072781057037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (36264479, 1), (38072781057037, 1)] : List FactorBlock).map factorBlockValue).prod) = 74557236732183868791043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_thirtyFiveAG_36264479
      · exact prime_thirtyFiveAG_38072781057037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 74557236732183868791043) ^ 37278618366091934395521 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74557236732183868791043) ^ 24852412244061289597014 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74557236732183868791043) ^ 2055930177079998 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 74557236732183868791043) ^ 1958281866 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_323825085837699689026691 : Nat.Prime 323825085837699689026691 := by
  apply lucas_primality 323825085837699689026691 (2 : ZMod 323825085837699689026691)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (132661, 1), (244099687050225529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (132661, 1), (244099687050225529, 1)] : List FactorBlock).map factorBlockValue).prod) = 323825085837699689026691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_thirtyFiveAG_132661
      · exact prime_thirtyFiveAG_244099687050225529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 323825085837699689026691) ^ 161912542918849844513345 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 323825085837699689026691) ^ 64765017167539937805338 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 323825085837699689026691) ^ 2440996870502255290 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (2 : ZMod 323825085837699689026691) ^ 1326610 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_527710213148314429532063 : Nat.Prime 527710213148314429532063 := by
  apply lucas_primality 527710213148314429532063 (5 : ZMod 527710213148314429532063)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (2077599264363442635953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (2077599264363442635953, 1)] : List FactorBlock).map factorBlockValue).prod) = 527710213148314429532063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_thirtyFiveAG_127
      · exact prime_thirtyFiveAG_2077599264363442635953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 527710213148314429532063) ^ 263855106574157214766031 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 527710213148314429532063) ^ 4155198528726885271906 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 527710213148314429532063) ^ 254 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_880280403846209699893583 : Nat.Prime 880280403846209699893583 := by
  apply lucas_primality 880280403846209699893583 (5 : ZMod 880280403846209699893583)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1997, 1), (3511, 1), (4349, 1), (1312200053707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1997, 1), (3511, 1), (4349, 1), (1312200053707, 1)] : List FactorBlock).map factorBlockValue).prod) = 880280403846209699893583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_1997
      · exact prime_t64_3511
      · exact prime_thirtyFiveAG_4349
      · exact prime_thirtyFiveAG_1312200053707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 880280403846209699893583) ^ 440140201923104849946791 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 880280403846209699893583) ^ 80025491258746336353962 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 880280403846209699893583) ^ 440801404029148572806 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 880280403846209699893583) ^ 250720707446940956962 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 880280403846209699893583) ^ 202409842227226879718 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 880280403846209699893583) ^ 670843139626 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_239
      · exact prime_thirtyFiveAG_4519
      · exact prime_thirtyFiveAG_15661
      · exact prime_thirtyFiveAG_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_thirtyFiveAG_1173959
      · exact prime_thirtyFiveAG_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_991
      · exact prime_thirtyFiveAG_3779417
      · exact prime_thirtyFiveAG_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_444939149931169670568792001 : Nat.Prime 444939149931169670568792001 := by
  apply lucas_primality 444939149931169670568792001 (79 : ZMod 444939149931169670568792001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 444939149931169670568792001 - 1 by
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
    · change (79 : ZMod 444939149931169670568792001) ^ 222469574965584835284396000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 148313049977056556856264000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 88987829986233934113758400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 63562735704452810081256000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 40449013630106333688072000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 34226088456243820812984000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 26172891172421745327576000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 23417849996377351082568000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 19345180431789985676904000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 15342729307971367950648000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 12025382430572153258616000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 10852174388565113916312000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 10347422091422550478344000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 9466790424067439799336000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 8395078300588106991864000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 7541341524257113060488000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (79 : ZMod 444939149931169670568792001) ^ 7294084425101142140472000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_504626109068277797108508001 : Nat.Prime 504626109068277797108508001 := by
  apply lucas_primality 504626109068277797108508001 (82 : ZMod 504626109068277797108508001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 504626109068277797108508001 - 1 by
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
    · change (82 : ZMod 504626109068277797108508001) ^ 252313054534138898554254000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 168208703022759265702836000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 100925221813655559421701600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 72089444152611113872644000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 45875100824388890646228000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 38817393005252138239116000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 29683888768722223359324000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 26559268898330410374132000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 21940265611664252048196000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 17400900312699234383052000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 16278261582847670874468000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 13638543488331832354284000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 11735490908564599932756000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 10736725724856974406564000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 9521247340910901832236000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 8552984899462335544212000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (82 : ZMod 504626109068277797108508001) ^ 8272559165053734378828000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_559180283021605126525644001 : Nat.Prime 559180283021605126525644001 := by
  apply lucas_primality 559180283021605126525644001 (73 : ZMod 559180283021605126525644001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 559180283021605126525644001 - 1 by
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
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 559180283021605126525644001) ^ 279590141510802563262822000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 186393427673868375508548000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 111836056604321025305128800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 79882897574515018075092000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 50834571183782284229604000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 43013867924738855886588000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 32892957824800301560332000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 29430541211663427711876000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 24312186218330657675028000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 19282078724882935397436000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 18038073645858229887924000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 13638543488331832354284000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 13004192628409421547108000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 11897452830246917585652000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 10550571377766134462748000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 9477631915620425873316000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (73 : ZMod 559180283021605126525644001) ^ 9166889885600084041404000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_678349851534406219063896001 : Nat.Prime 678349851534406219063896001 := by
  apply lucas_primality 678349851534406219063896001 (109 : ZMod 678349851534406219063896001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 678349851534406219063896001 - 1 by
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
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (109 : ZMod 678349851534406219063896001) ^ 339174925767203109531948000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 226116617178135406354632000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 135669970306881243812779200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 96907121647772317009128000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 61668168321309656278536000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 52180757810338939927992000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 39902932443200365827288000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 35702623764968748371784000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 29493471805843748654952000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 23391374190841593760824000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 21882253275303426421416000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 18333779771200168082808000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 16545118330107468757656000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 15775577942660609745672000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 14432975564561834448168000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 12799053802535966397432000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (109 : ZMod 678349851534406219063896001) ^ 11497455110752647780744000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 752351653519977806598139201 - 1 by
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
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 919540909857750652508836801 - 1 by
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
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1088930024831546825339412001 : Nat.Prime 1088930024831546825339412001 := by
  apply lucas_primality 1088930024831546825339412001 (57 : ZMod 1088930024831546825339412001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088930024831546825339412001 - 1 by
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
    · change (57 : ZMod 1088930024831546825339412001) ^ 544465012415773412669706000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 362976674943848941779804000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 217786004966309365067882400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 155561432118792403619916000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 98993638621049711394492000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 83763848063965140410724000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 64054707343032166196436000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 47344783688328122840844000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 37549311201087821563428000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 35126774994566026623852000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 29430541211663427711876000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 26559268898330410374132000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 25323954065849926170684000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 23168723932586102666796000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 20545849525123525006404000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 18456441098839776700668000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (57 : ZMod 1088930024831546825339412001) ^ 17851311882484374185892000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1118360566043210253051288001 : Nat.Prime 1118360566043210253051288001 := by
  apply lucas_primality 1118360566043210253051288001 (149 : ZMod 1118360566043210253051288001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118360566043210253051288001 - 1 by
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
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (149 : ZMod 1118360566043210253051288001) ^ 559180283021605126525644000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 372786855347736751017096000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 223672113208642050610257600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 159765795149030036150184000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 101669142367564568459208000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 86027735849477711773176000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 65785915649600603120664000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 58861082423326855423752000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 48624372436661315350056000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 38564157449765870794872000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 36076147291716459775848000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 27277086976663664708568000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 26008385256818843094216000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 23794905660493835171304000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 21101142755532268925496000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 18955263831240851746632000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (149 : ZMod 1118360566043210253051288001) ^ 18333779771200168082808000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1217039439517611157732284001 : Nat.Prime 1217039439517611157732284001 := by
  apply lucas_primality 1217039439517611157732284001 (101 : ZMod 1217039439517611157732284001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1217039439517611157732284001 - 1 by
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
    · change (101 : ZMod 1217039439517611157732284001) ^ 608519719758805578866142000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 405679813172537052577428000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 243407887903522231546456800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 173862777073944451104612000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 110639949047055559793844000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 93618418424431627517868000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 64054707343032166196436000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 52914758239896137292708000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 41966877224745212335596000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 39259336758632617991364000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 32892957824800301560332000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 29683888768722223359324000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 28303242779479329249588000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 25894456159949173568772000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 22963008292785116183628000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 20627787110467985724276000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (101 : ZMod 1217039439517611157732284001) ^ 19951466221600182913644000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1293104404487461855090551751 : Nat.Prime 1293104404487461855090551751 := by
  apply lucas_primality 1293104404487461855090551751 (11 : ZMod 1293104404487461855090551751)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293104404487461855090551751 - 1 by
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
    · change (11 : ZMod 1293104404487461855090551751) ^ 646552202243730927545275875 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 431034801495820618363517250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 258620880897492371018110350 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 184729200641065979298650250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 117554945862496532280959250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 99469569575958604237734750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 76064964969850697358267750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 68058126551971676583713250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 56221930629889645873502250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 44589807051291788106570750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 41713045306047156615824250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 34948767688850320407852750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 31539131816767362319281750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 30072195453196787327687250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 27512859669945996916820250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 24398196311084185945104750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 21917023804872234832043250 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1293104404487461855090551751) ^ 21198432860450194345746750 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
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
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_1880879133799944516495348001 : Nat.Prime 1880879133799944516495348001 := by
  apply lucas_primality 1880879133799944516495348001 (97 : ZMod 1880879133799944516495348001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 3), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 3), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880879133799944516495348001 - 1 by
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
    · change (97 : ZMod 1880879133799944516495348001) ^ 940439566899972258247674000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 626959711266648172165116000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 376175826759988903299069600 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 268697019114277788070764000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 144683010292303424345796000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 110639949047055559793844000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 98993638621049711394492000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 81777353643475848543276000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 64857901165515328155012000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 60673520445159500532108000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 50834571183782284229604000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 45875100824388890646228000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 43741375204649872476636000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 40018704974466904606284000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 35488285543395179556516000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 31879307352541432482972000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (97 : ZMod 1880879133799944516495348001) ^ 30834084160654828139268000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_10344835235899694840724414001 : Nat.Prime 10344835235899694840724414001 := by
  apply lucas_primality 10344835235899694840724414001 (107 : ZMod 10344835235899694840724414001)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10344835235899694840724414001 - 1 by
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
    · change (107 : ZMod 10344835235899694840724414001) ^ 5172417617949847420362207000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 3448278411966564946908138000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 2068967047179938968144882800 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 1477833605128527834389202000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 940439566899972258247674000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 795756556607668833901878000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 608519719758805578866142000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 544465012415773412669706000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 449775445039117166988018000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 356718456410334304852566000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 333704362448377252926594000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 279590141510802563262822000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 252313054534138898554254000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 240577563625574298621498000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 220102877359567975334562000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 195185570488673487560838000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 175336190438977878656346000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (107 : ZMod 10344835235899694840724414001) ^ 169587462883601554765974000 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem prime_thirtyFiveAG_41379340943598779362897656079 : Nat.Prime 41379340943598779362897656079 := by
  apply lucas_primality 41379340943598779362897656079 (3 : ZMod 41379340943598779362897656079)
  · rw [← thirtyFiveAGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (689341, 1), (769581921098236174261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (689341, 1), (769581921098236174261, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_thirtyFiveAG_689341
      · exact prime_thirtyFiveAG_769581921098236174261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41379340943598779362897656079) ^ 20689670471799389681448828039 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41379340943598779362897656079) ^ 13793113647866259787632552026 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41379340943598779362897656079) ^ 3183026226430675335607512006 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41379340943598779362897656079) ^ 60027389845662421592358 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide
    · change (3 : ZMod 41379340943598779362897656079) ^ 53768598 ≠ 1
      rw [← thirtyFiveAGFastPow_eq_pow]
      decide

private theorem phi_thirtyFiveAG_41379340943598779362897655999 : Nat.totient 41379340943598779362897655999 = 41266561327226965432231056000 := by
  rw [← show ((([(607, 1), (971, 1), (19997, 1), (63375941, 1), (55397017171, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897655999 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_607, prime_thirtyFiveAG_971, prime_thirtyFiveAG_19997, prime_thirtyFiveAG_63375941, prime_thirtyFiveAG_55397017171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656000 : Nat.totient 41379340943598779362897656000 = 5444997896077622378496000000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656001 : Nat.totient 41379340943598779362897656001 = 40855548769265705152921083360 := by
  rw [← show ((([(79, 1), (13402009, 1), (39082881220893000391, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_79, prime_thirtyFiveAG_13402009, prime_thirtyFiveAG_39082881220893000391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656002 : Nat.totient 41379340943598779362897656002 = 20641665625824622466439687360 := by
  rw [← show ((([(2, 1), (431, 1), (21276337, 1), (2256209600582983583, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_431, prime_thirtyFiveAG_21276337, prime_thirtyFiveAG_2256209600582983583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656003 : Nat.totient 41379340943598779362897656003 = 27586225808440560911935895904 := by
  rw [← show ((([(3, 1), (18547957, 1), (743645979331646056093, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyFiveAG_18547957, prime_thirtyFiveAG_743645979331646056093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656004 : Nat.totient 41379340943598779362897656004 = 20689670471799389681448828000 := by
  rw [← show ((([(2, 2), (10344835235899694840724414001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_thirtyFiveAG_10344835235899694840724414001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656005 : Nat.totient 41379340943598779362897656005 = 33103213093323297188628106768 := by
  rw [← show ((([(5, 1), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_thirtyFiveAG_127487, prime_thirtyFiveAG_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656006 : Nat.totient 41379340943598779362897656006 = 13548664203699843541422489600 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1), (271, 1), (234156128057, 1), (1530731964673, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_71, prime_thirtyFiveAG_271, prime_thirtyFiveAG_234156128057, prime_thirtyFiveAG_1530731964673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656007 : Nat.totient 41379340943598779362897656007 = 35467759647446283316344663072 := by
  rw [← show ((([(7, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_thirtyFiveAG_143669, prime_thirtyFiveAG_13852339783, prime_thirtyFiveAG_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656008 : Nat.totient 41379340943598779362897656008 = 20538386381206716703567324992 := by
  rw [← show ((([(2, 3), (139, 1), (10667, 1), (40123, 1), (86944695168309299, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_139, prime_thirtyFiveAG_10667, prime_thirtyFiveAG_40123, prime_thirtyFiveAG_86944695168309299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656009 : Nat.totient 41379340943598779362897656009 = 27586171508222610918238500000 := by
  rw [← show ((([(3, 2), (562501, 1), (4089619, 1), (1998641547176479, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyFiveAG_562501, prime_thirtyFiveAG_4089619, prime_thirtyFiveAG_1998641547176479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656010 : Nat.totient 41379340943598779362897656010 = 16551690856989422392767979600 := by
  rw [← show ((([(2, 1), (5, 1), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_thirtyFiveAG_363611, prime_thirtyFiveAG_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656011 : Nat.totient 41379340943598779362897656011 = 37203840846884533880872800000 := by
  rw [← show ((([(11, 1), (151, 1), (227, 1), (323190492101, 1), (339570147913, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_thirtyFiveAG_151, prime_t64_227, prime_thirtyFiveAG_323190492101, prime_thirtyFiveAG_339570147913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656012 : Nat.totient 41379340943598779362897656012 = 13793112360680216055516307600 := by
  rw [← show ((([(2, 2), (3, 1), (10715711, 1), (321796510933018345391, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_10715711, prime_thirtyFiveAG_321796510933018345391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656013 : Nat.totient 41379340943598779362897656013 = 38196074927421319192509335040 := by
  rw [← show ((([(13, 1), (159293, 1), (11935203661, 1), (1674224493737, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_thirtyFiveAG_159293, prime_thirtyFiveAG_11935203661, prime_thirtyFiveAG_1674224493737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656014 : Nat.totient 41379340943598779362897656014 = 17650851454747358758890445824 := by
  rw [← show ((([(2, 1), (7, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_223, prime_thirtyFiveAG_5113, prime_thirtyFiveAG_101287, prime_thirtyFiveAG_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656015 : Nat.totient 41379340943598779362897656015 = 21907894377924803867071847936 := by
  rw [← show ((([(3, 1), (5, 1), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_137, prime_thirtyFiveAG_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656016 : Nat.totient 41379340943598779362897656016 = 20689670471797247088154880736 := by
  rw [← show ((([(2, 4), (10032152737987, 1), (257792009005423, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_thirtyFiveAG_10032152737987, prime_thirtyFiveAG_257792009005423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656017 : Nat.totient 41379340943598779362897656017 = 38578786556764821359684823040 := by
  rw [← show ((([(17, 1), (107, 1), (15497, 1), (3355031, 1), (437528854855949, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_107, prime_thirtyFiveAG_15497, prime_thirtyFiveAG_3355031, prime_thirtyFiveAG_437528854855949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656018 : Nat.totient 41379340943598779362897656018 = 13716808439381452125350219520 := by
  rw [← show ((([(2, 1), (3, 2), (181, 1), (136949, 1), (92741394945401364329, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_181, prime_thirtyFiveAG_136949, prime_thirtyFiveAG_92741394945401364329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656019 : Nat.totient 41379340943598779362897656019 = 39191982110099016052487180616 := by
  rw [← show ((([(19, 1), (4127, 1), (527710213148314429532063, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_thirtyFiveAG_4127, prime_thirtyFiveAG_527710213148314429532063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656020 : Nat.totient 41379340943598779362897656020 = 16543997288938364065731985536 := by
  rw [← show ((([(2, 2), (5, 1), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_thirtyFiveAG_3023, prime_thirtyFiveAG_7309, prime_thirtyFiveAG_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656021 : Nat.totient 41379340943598779362897656021 = 23321426909210346488422003200 := by
  rw [← show ((([(3, 1), (7, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_73, prime_thirtyFiveAG_13737811, prime_thirtyFiveAG_68784581, prime_thirtyFiveAG_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656022 : Nat.totient 41379340943598779362897656022 = 18808791337999445164953480000 := by
  rw [← show ((([(2, 1), (11, 1), (1880879133799944516495348001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_thirtyFiveAG_1880879133799944516495348001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656023 : Nat.totient 41379340943598779362897656023 = 39576520936886947152501051360 := by
  rw [← show ((([(23, 1), (15299, 1), (42787, 1), (192007, 1), (14314091514911, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_thirtyFiveAG_15299, prime_thirtyFiveAG_42787, prime_thirtyFiveAG_192007, prime_thirtyFiveAG_14314091514911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656024 : Nat.totient 41379340943598779362897656024 = 13703918790914373532425383040 := by
  rw [← show ((([(2, 3), (3, 1), (157, 1), (10223, 1), (1074222672606781183091, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_157, prime_thirtyFiveAG_10223, prime_thirtyFiveAG_1074222672606781183091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656025 : Nat.totient 41379340943598779362897656025 = 32731523622801731091550503680 := by
  rw [← show ((([(5, 2), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_89, prime_thirtyFiveAG_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656026 : Nat.totient 41379340943598779362897656026 = 19097327400852593839205890800 := by
  rw [← show ((([(2, 1), (13, 1), (23011, 1), (69163144288181203242091, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_thirtyFiveAG_23011, prime_thirtyFiveAG_69163144288181203242091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656027 : Nat.totient 41379340943598779362897656027 = 27577727030097219526418160000 := by
  rw [← show ((([(3, 5), (5749, 1), (7451, 1), (236939771, 1), (16777701341, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyFiveAG_5749, prime_thirtyFiveAG_7451, prime_thirtyFiveAG_236939771, prime_thirtyFiveAG_16777701341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656028 : Nat.totient 41379340943598779362897656028 = 17734003261542334012670424000 := by
  rw [← show ((([(2, 2), (7, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_thirtyFiveAG_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656029 : Nat.totient 41379340943598779362897656029 = 39950507607087955781127534912 := by
  rw [← show ((([(29, 1), (20389, 1), (69982531053084369974509, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_thirtyFiveAG_20389, prime_thirtyFiveAG_69982531053084369974509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656030 : Nat.totient 41379340943598779362897656030 = 10992151663418071671083919360 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_263, prime_thirtyFiveAG_33811, prime_thirtyFiveAG_189853, prime_thirtyFiveAG_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656031 : Nat.totient 41379340943598779362897656031 = 40043189905216721943334675200 := by
  rw [← show ((([(31, 1), (30071, 1), (20826023, 1), (2131413249403297, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_thirtyFiveAG_30071, prime_thirtyFiveAG_20826023, prime_thirtyFiveAG_2131413249403297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656032 : Nat.totient 41379340943598779362897656032 = 20689670471799389681448828000 := by
  rw [← show ((([(2, 5), (1293104404487461855090551751, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_thirtyFiveAG_1293104404487461855090551751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656033 : Nat.totient 41379340943598779362897656033 = 25078388450664358693849518080 := by
  rw [← show ((([(3, 1), (11, 1), (22379290632929, 1), (56030347123169, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_thirtyFiveAG_22379290632929, prime_thirtyFiveAG_56030347123169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656034 : Nat.totient 41379340943598779362897656034 = 19472631032281778523716544000 := by
  rw [← show ((([(2, 1), (17, 1), (1217039439517611157732284001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_thirtyFiveAG_1217039439517611157732284001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656035 : Nat.totient 41379340943598779362897656035 = 28093315868479095348023428608 := by
  rw [← show ((([(5, 1), (7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656036 : Nat.totient 41379340943598779362897656036 = 13791557351240095043889284544 := by
  rw [← show ((([(2, 2), (3, 2), (8863, 1), (356006269, 1), (364286161507483, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_8863, prime_thirtyFiveAG_356006269, prime_thirtyFiveAG_364286161507483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656037 : Nat.totient 41379340943598779362897656037 = 40260980377555569109846368000 := by
  rw [← show ((([(37, 1), (1118360566043210253051288001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_thirtyFiveAG_1118360566043210253051288001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656038 : Nat.totient 41379340943598779362897656038 = 19600740446967842856109416000 := by
  rw [← show ((([(2, 1), (19, 1), (1088930024831546825339412001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_thirtyFiveAG_1088930024831546825339412001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656039 : Nat.totient 41379340943598779362897656039 = 25435306054101404946850928640 := by
  rw [← show ((([(3, 1), (13, 1), (881, 1), (54977560373, 1), (21905722901677, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_thirtyFiveAG_881, prime_thirtyFiveAG_54977560373, prime_thirtyFiveAG_21905722901677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656040 : Nat.totient 41379340943598779362897656040 = 16465976085328426192075333632 := by
  rw [← show ((([(2, 3), (5, 1), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_193, prime_thirtyFiveAG_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656041 : Nat.totient 41379340943598779362897656041 = 40366545032668749477114470400 := by
  rw [← show ((([(41, 1), (19009, 1), (28429, 1), (1867578469061212741, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_thirtyFiveAG_19009, prime_thirtyFiveAG_28429, prime_thirtyFiveAG_1867578469061212741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656042 : Nat.totient 41379340943598779362897656042 = 11761536323008053982600445952 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_283, prime_thirtyFiveAG_613, prime_thirtyFiveAG_85303, prime_thirtyFiveAG_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656043 : Nat.totient 41379340943598779362897656043 = 40413899285153730445921898184 := by
  rw [← show ((([(43, 1), (12907, 1), (74557236732183868791043, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_thirtyFiveAG_12907, prime_thirtyFiveAG_74557236732183868791043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656044 : Nat.totient 41379340943598779362897656044 = 18808272645486394891144978560 := by
  rw [← show ((([(2, 2), (11, 1), (36899, 1), (2100227, 1), (12135287197724137, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_thirtyFiveAG_36899, prime_thirtyFiveAG_2100227, prime_thirtyFiveAG_12135287197724137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656045 : Nat.totient 41379340943598779362897656045 = 22068981836586015660212083200 := by
  rw [← show ((([(3, 2), (5, 1), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_thirtyFiveAG_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656046 : Nat.totient 41379340943598779362897656046 = 19779034333475987132774800512 := by
  rw [← show ((([(2, 1), (23, 2), (1787, 1), (2567303, 1), (6515723, 1), (1308379129, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_thirtyFiveAG_1787, prime_thirtyFiveAG_2567303, prime_thirtyFiveAG_6515723, prime_thirtyFiveAG_1308379129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656047 : Nat.totient 41379340943598779362897656047 = 40096609031318831590850944000 := by
  rw [← show ((([(47, 1), (101, 1), (29921, 1), (51660683, 1), (5639337539207, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_101, prime_thirtyFiveAG_29921, prime_thirtyFiveAG_51660683, prime_thirtyFiveAG_5639337539207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656048 : Nat.totient 41379340943598779362897656048 = 13790600690948203011572035584 := by
  rw [← show ((([(2, 4), (3, 1), (5657, 1), (186023, 1), (23612227, 1), (34693855033, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_5657, prime_thirtyFiveAG_186023, prime_thirtyFiveAG_23612227, prime_thirtyFiveAG_34693855033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656049 : Nat.totient 41379340943598779362897656049 = 35153484032890152056223129600 := by
  rw [← show ((([(7, 2), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_113, prime_thirtyFiveAG_54421, prime_thirtyFiveAG_97654321, prime_thirtyFiveAG_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656050 : Nat.totient 41379340943598779362897656050 = 16380791550376859269368576000 := by
  rw [← show ((([(2, 1), (5, 2), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_97, prime_thirtyFiveAG_72973, prime_thirtyFiveAG_195271, prime_thirtyFiveAG_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656051 : Nat.totient 41379340943598779362897656051 = 25785540420001121922795584000 := by
  rw [← show ((([(3, 1), (17, 1), (251, 1), (347, 1), (9690287, 1), (961332349927559, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_251, prime_thirtyFiveAG_347, prime_thirtyFiveAG_9690287, prime_thirtyFiveAG_961332349927559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656052 : Nat.totient 41379340943598779362897656052 = 19095692484980211653259463680 := by
  rw [← show ((([(2, 2), (13, 1), (8053, 1), (225611, 1), (2201209, 1), (198976128383, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_thirtyFiveAG_8053, prime_thirtyFiveAG_225611, prime_thirtyFiveAG_2201209, prime_thirtyFiveAG_198976128383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656053 : Nat.totient 41379340943598779362897656053 = 40581759757180525028824790800 := by
  rw [← show ((([(53, 1), (2411, 1), (323825085837699689026691, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_thirtyFiveAG_2411, prime_thirtyFiveAG_323825085837699689026691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656054 : Nat.totient 41379340943598779362897656054 = 13749040947358397596873950720 := by
  rw [← show ((([(2, 1), (3, 3), (313, 1), (4614439, 1), (6070121, 1), (87403578583, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_313, prime_thirtyFiveAG_4614439, prime_thirtyFiveAG_6070121, prime_thirtyFiveAG_87403578583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656055 : Nat.totient 41379340943598779362897656055 = 30094066140799112263925568000 := by
  rw [← show ((([(5, 1), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_thirtyFiveAG_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656056 : Nat.totient 41379340943598779362897656056 = 17520328186295811462437913600 := by
  rw [← show ((([(2, 3), (7, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_83, prime_thirtyFiveAG_1433741, prime_thirtyFiveAG_106163831, prime_thirtyFiveAG_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656057 : Nat.totient 41379340943598779362897656057 = 25684258530530316581191286784 := by
  rw [← show ((([(3, 1), (19, 1), (67, 1), (433, 1), (47387, 1), (528064289915195393, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_t64_67, prime_t64_433, prime_thirtyFiveAG_47387, prime_thirtyFiveAG_528064289915195393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656058 : Nat.totient 41379340943598779362897656058 = 19940751732139465952293282560 := by
  rw [← show ((([(2, 1), (29, 1), (563, 1), (321206161, 1), (3945148126310507, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_t64_563, prime_thirtyFiveAG_321206161, prime_thirtyFiveAG_3945148126310507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656059 : Nat.totient 41379340943598779362897656059 = 40646322566316696410699760000 := by
  rw [← show ((([(59, 1), (2251, 1), (5557, 1), (6491, 1), (1788539, 1), (4829538607, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_t64_2251, prime_thirtyFiveAG_5557, prime_thirtyFiveAG_6491, prime_thirtyFiveAG_1788539, prime_thirtyFiveAG_4829538607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656060 : Nat.totient 41379340943598779362897656060 = 10903261327251748374695526400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_thirtyFiveAG_131, prime_t64_233, prime_thirtyFiveAG_550990241, prime_thirtyFiveAG_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656061 : Nat.totient 41379340943598779362897656061 = 40700991092064373143833760000 := by
  rw [← show ((([(61, 1), (678349851534406219063896001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_thirtyFiveAG_678349851534406219063896001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656062 : Nat.totient 41379340943598779362897656062 = 20022261746837085439313180160 := by
  rw [← show ((([(2, 1), (31, 1), (305494158833, 1), (2184685715256497, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_thirtyFiveAG_305494158833, prime_thirtyFiveAG_2184685715256497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656063 : Nat.totient 41379340943598779362897656063 = 23603129182732107111598729728 := by
  rw [← show ((([(3, 2), (7, 1), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_thirtyFiveAG_569, prime_thirtyFiveAG_37039, prime_thirtyFiveAG_1544987, prime_thirtyFiveAG_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656064 : Nat.totient 41379340943598779362897656064 = 20641914679611257980175646720 := by
  rw [← show ((([(2, 8), (439, 1), (41621, 1), (157889, 1), (56029235811859, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_439, prime_thirtyFiveAG_41621, prime_thirtyFiveAG_157889, prime_thirtyFiveAG_56029235811859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656065 : Nat.totient 41379340943598779362897656065 = 30554111050822950695290954560 := by
  rw [← show ((([(5, 1), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_thirtyFiveAG_10391, prime_thirtyFiveAG_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656066 : Nat.totient 41379340943598779362897656066 = 12510889046494740049524044240 := by
  rw [← show ((([(2, 1), (3, 1), (11, 3), (443, 1), (11696354891827848668267, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_thirtyFiveAG_443, prime_thirtyFiveAG_11696354891827848668267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656067 : Nat.totient 41379340943598779362897656067 = 41379340898427203172320265600 := by
  rw [← show ((([(1531293541, 1), (3080754007, 1), (8771383441, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_1531293541, prime_thirtyFiveAG_3080754007, prime_thirtyFiveAG_8771383441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656068 : Nat.totient 41379340943598779362897656068 = 19384532295197743210347233280 := by
  rw [← show ((([(2, 2), (17, 1), (353, 1), (907, 1), (1753, 1), (41911, 1), (25869183698957, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_thirtyFiveAG_353, prime_thirtyFiveAG_907, prime_thirtyFiveAG_1753, prime_thirtyFiveAG_41911, prime_thirtyFiveAG_25869183698957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656069 : Nat.totient 41379340943598779362897656069 = 26296750716957862118566617600 := by
  rw [← show ((([(3, 1), (23, 1), (293, 1), (1498121, 1), (64043047, 1), (21332805811, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_thirtyFiveAG_293, prime_thirtyFiveAG_1498121, prime_thirtyFiveAG_64043047, prime_thirtyFiveAG_21332805811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656070 : Nat.totient 41379340943598779362897656070 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656071 : Nat.totient 41379340943598779362897656071 = 41377504487561220639622852800 := by
  rw [← show ((([(34217, 1), (65983, 1), (1439312431, 1), (12733696831, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_34217, prime_thirtyFiveAG_65983, prime_thirtyFiveAG_1439312431, prime_thirtyFiveAG_12733696831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656072 : Nat.totient 41379340943598779362897656072 = 13723801518618511788958288128 := by
  rw [← show ((([(2, 3), (3, 2), (199, 1), (37721539993, 1), (76561173554743, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_thirtyFiveAG_199, prime_thirtyFiveAG_37721539993, prime_thirtyFiveAG_76561173554743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656073 : Nat.totient 41379340943598779362897656073 = 41379053823522385047733533360 := by
  rw [← show ((([(220471, 1), (416147, 1), (451009125414846629, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_220471, prime_thirtyFiveAG_416147, prime_thirtyFiveAG_451009125414846629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656074 : Nat.totient 41379340943598779362897656074 = 20130490188777784554923184000 := by
  rw [← show ((([(2, 1), (37, 1), (559180283021605126525644001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_thirtyFiveAG_559180283021605126525644001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656075 : Nat.totient 41379340943598779362897656075 = 22068981835700183404903637280 := by
  rw [← show ((([(3, 1), (5, 2), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_thirtyFiveAG_24913302187, prime_thirtyFiveAG_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656076 : Nat.totient 41379340943598779362897656076 = 19561772742233821239070492992 := by
  rw [← show ((([(2, 2), (19, 1), (503, 1), (654477533, 1), (1653892391684899, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_thirtyFiveAG_503, prime_thirtyFiveAG_654477533, prime_thirtyFiveAG_1653892391684899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656077 : Nat.totient 41379340943598779362897656077 = 31789506485568330350201750400 := by
  rw [← show ((([(7, 1), (11, 1), (71, 1), (26687336297, 1), (283615046165023, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_71, prime_thirtyFiveAG_26687336297, prime_thirtyFiveAG_283615046165023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656078 : Nat.totient 41379340943598779362897656078 = 12732086435756594984745321600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (689341, 1), (769581921098236174261, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_thirtyFiveAG_689341, prime_thirtyFiveAG_769581921098236174261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656079 : Nat.totient 41379340943598779362897656079 = 41379340943598779362897656078 := by
  rw [← show ((([(41379340943598779362897656079, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_41379340943598779362897656079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656080 : Nat.totient 41379340943598779362897656080 = 16339597154564897015566073856 := by
  rw [← show ((([(2, 4), (5, 1), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_79, prime_thirtyFiveAG_6229, prime_thirtyFiveAG_8696692033, prime_thirtyFiveAG_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656081 : Nat.totient 41379340943598779362897656081 = 27570382248463287800666988240 := by
  rw [← show ((([(3, 3), (1741, 1), (880280403846209699893583, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_thirtyFiveAG_1741, prime_thirtyFiveAG_880280403846209699893583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656082 : Nat.totient 41379340943598779362897656082 = 20185044362731111884340320000 := by
  rw [← show ((([(2, 1), (41, 1), (504626109068277797108508001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_thirtyFiveAG_504626109068277797108508001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656083 : Nat.totient 41379340943598779362897656083 = 41379298530610908359903367528 := by
  rw [← show ((([(975629, 1), (42412987871002993312927, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_975629, prime_thirtyFiveAG_42412987871002993312927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656084 : Nat.totient 41379340943598779362897656084 = 11714188603258043153623613952 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (109, 1), (762563, 1), (500452427, 1), (11842387189, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_109, prime_thirtyFiveAG_762563, prime_thirtyFiveAG_500452427, prime_thirtyFiveAG_11842387189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656085 : Nat.totient 41379340943598779362897656085 = 31156186510117769013544004608 := by
  rw [← show ((([(5, 1), (17, 1), (1346333, 1), (361586454322254942197, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_thirtyFiveAG_1346333, prime_thirtyFiveAG_361586454322254942197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656086 : Nat.totient 41379340943598779362897656086 = 20206167971890535112606024960 := by
  rw [← show ((([(2, 1), (43, 1), (8609, 1), (10987937171, 1), (5086467135259, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_thirtyFiveAG_8609, prime_thirtyFiveAG_10987937171, prime_thirtyFiveAG_5086467135259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656087 : Nat.totient 41379340943598779362897656087 = 26634978075365745720100024832 := by
  rw [← show ((([(3, 1), (29, 1), (8138909897, 1), (58438367615106233, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_thirtyFiveAG_8138909897, prime_thirtyFiveAG_58438367615106233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656088 : Nat.totient 41379340943598779362897656088 = 18779716364297253677655045120 := by
  rw [← show ((([(2, 3), (11, 1), (647, 1), (5601139, 1), (22283273, 1), (5822926189, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_647, prime_thirtyFiveAG_5601139, prime_thirtyFiveAG_22283273, prime_thirtyFiveAG_5822926189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656089 : Nat.totient 41379340943598779362897656089 = 40716276277337238209750067600 := by
  rw [← show ((([(163, 1), (191, 1), (211, 1), (6299123778170308210303, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_163, prime_t64_191, prime_thirtyFiveAG_211, prime_thirtyFiveAG_6299123778170308210303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656090 : Nat.totient 41379340943598779362897656090 = 11005731768077896458884520960 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (521, 1), (1453, 1), (607348163015529886877, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_521, prime_thirtyFiveAG_1453, prime_thirtyFiveAG_607348163015529886877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656091 : Nat.totient 41379340943598779362897656091 = 32666026785447365436462336000 := by
  rw [← show ((([(7, 1), (13, 1), (599, 1), (1811, 1), (33809, 1), (12398369604474701, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_thirtyFiveAG_599, prime_thirtyFiveAG_1811, prime_thirtyFiveAG_33809, prime_thirtyFiveAG_12398369604474701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656092 : Nat.totient 41379340943598779362897656092 = 19633584094245363246260256000 := by
  rw [← show ((([(2, 2), (23, 1), (127, 1), (27743, 1), (366269941, 1), (348527716301, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_thirtyFiveAG_127, prime_thirtyFiveAG_27743, prime_thirtyFiveAG_366269941, prime_thirtyFiveAG_348527716301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656093 : Nat.totient 41379340943598779362897656093 = 26696348995870180234127520000 := by
  rw [← show ((([(3, 1), (31, 1), (444939149931169670568792001, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_thirtyFiveAG_444939149931169670568792001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656094 : Nat.totient 41379340943598779362897656094 = 19972058374886046121827459072 := by
  rw [← show ((([(2, 1), (47, 1), (73, 1), (1216729, 1), (4956087853639023553, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_t64_73, prime_thirtyFiveAG_1216729, prime_thirtyFiveAG_4956087853639023553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656095 : Nat.totient 41379340943598779362897656095 = 31361184706924831413473344800 := by
  rw [← show ((([(5, 1), (19, 1), (3813504911, 1), (114218290024018991, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_thirtyFiveAG_3813504911, prime_thirtyFiveAG_114218290024018991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656096 : Nat.totient 41379340943598779362897656096 = 13674617725495924155746304000 := by
  rw [← show ((([(2, 5), (3, 1), (179, 1), (331, 1), (11564851, 1), (629058839990849, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_179, prime_thirtyFiveAG_331, prime_thirtyFiveAG_11564851, prime_thirtyFiveAG_629058839990849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656097 : Nat.totient 41379340943598779362897656097 = 41377962137488515936901078800 := by
  rw [← show ((([(30011, 1), (136330035181, 1), (10113734664767, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtyFiveAG_30011, prime_thirtyFiveAG_136330035181, prime_thirtyFiveAG_10113734664767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtyFiveAG_41379340943598779362897656098 : Nat.totient 41379340943598779362897656098 = 17734003250931232773620074368 := by
  rw [← show ((([(2, 1), (7, 2), (1671268889, 1), (252645265925168009, 1)] : List FactorBlock).map factorBlockValue).prod) = 41379340943598779362897656098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_thirtyFiveAG_1671268889, prime_thirtyFiveAG_252645265925168009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtyFiveAG : certifiedKill 1 41379340943598779362897655998 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtyFiveAG_41379340943598779362897655999, phi_thirtyFiveAG_41379340943598779362897656000, phi_thirtyFiveAG_41379340943598779362897656001,
    phi_thirtyFiveAG_41379340943598779362897656002, phi_thirtyFiveAG_41379340943598779362897656003, phi_thirtyFiveAG_41379340943598779362897656004,
    phi_thirtyFiveAG_41379340943598779362897656005, phi_thirtyFiveAG_41379340943598779362897656006, phi_thirtyFiveAG_41379340943598779362897656007,
    phi_thirtyFiveAG_41379340943598779362897656008, phi_thirtyFiveAG_41379340943598779362897656009, phi_thirtyFiveAG_41379340943598779362897656010,
    phi_thirtyFiveAG_41379340943598779362897656011, phi_thirtyFiveAG_41379340943598779362897656012, phi_thirtyFiveAG_41379340943598779362897656013,
    phi_thirtyFiveAG_41379340943598779362897656014, phi_thirtyFiveAG_41379340943598779362897656015, phi_thirtyFiveAG_41379340943598779362897656016,
    phi_thirtyFiveAG_41379340943598779362897656017, phi_thirtyFiveAG_41379340943598779362897656018, phi_thirtyFiveAG_41379340943598779362897656019,
    phi_thirtyFiveAG_41379340943598779362897656020, phi_thirtyFiveAG_41379340943598779362897656021, phi_thirtyFiveAG_41379340943598779362897656022,
    phi_thirtyFiveAG_41379340943598779362897656023, phi_thirtyFiveAG_41379340943598779362897656024, phi_thirtyFiveAG_41379340943598779362897656025,
    phi_thirtyFiveAG_41379340943598779362897656026, phi_thirtyFiveAG_41379340943598779362897656027, phi_thirtyFiveAG_41379340943598779362897656028,
    phi_thirtyFiveAG_41379340943598779362897656029, phi_thirtyFiveAG_41379340943598779362897656030, phi_thirtyFiveAG_41379340943598779362897656031,
    phi_thirtyFiveAG_41379340943598779362897656032, phi_thirtyFiveAG_41379340943598779362897656033, phi_thirtyFiveAG_41379340943598779362897656034,
    phi_thirtyFiveAG_41379340943598779362897656035, phi_thirtyFiveAG_41379340943598779362897656036, phi_thirtyFiveAG_41379340943598779362897656037,
    phi_thirtyFiveAG_41379340943598779362897656038, phi_thirtyFiveAG_41379340943598779362897656039, phi_thirtyFiveAG_41379340943598779362897656040,
    phi_thirtyFiveAG_41379340943598779362897656041, phi_thirtyFiveAG_41379340943598779362897656042, phi_thirtyFiveAG_41379340943598779362897656043,
    phi_thirtyFiveAG_41379340943598779362897656044, phi_thirtyFiveAG_41379340943598779362897656045, phi_thirtyFiveAG_41379340943598779362897656046,
    phi_thirtyFiveAG_41379340943598779362897656047, phi_thirtyFiveAG_41379340943598779362897656048, phi_thirtyFiveAG_41379340943598779362897656049,
    phi_thirtyFiveAG_41379340943598779362897656050, phi_thirtyFiveAG_41379340943598779362897656051, phi_thirtyFiveAG_41379340943598779362897656052,
    phi_thirtyFiveAG_41379340943598779362897656053, phi_thirtyFiveAG_41379340943598779362897656054, phi_thirtyFiveAG_41379340943598779362897656055,
    phi_thirtyFiveAG_41379340943598779362897656056, phi_thirtyFiveAG_41379340943598779362897656057, phi_thirtyFiveAG_41379340943598779362897656058,
    phi_thirtyFiveAG_41379340943598779362897656059, phi_thirtyFiveAG_41379340943598779362897656060, phi_thirtyFiveAG_41379340943598779362897656061,
    phi_thirtyFiveAG_41379340943598779362897656062, phi_thirtyFiveAG_41379340943598779362897656063, phi_thirtyFiveAG_41379340943598779362897656064,
    phi_thirtyFiveAG_41379340943598779362897656065, phi_thirtyFiveAG_41379340943598779362897656066, phi_thirtyFiveAG_41379340943598779362897656067,
    phi_thirtyFiveAG_41379340943598779362897656068, phi_thirtyFiveAG_41379340943598779362897656069, phi_thirtyFiveAG_41379340943598779362897656070,
    phi_thirtyFiveAG_41379340943598779362897656071, phi_thirtyFiveAG_41379340943598779362897656072, phi_thirtyFiveAG_41379340943598779362897656073,
    phi_thirtyFiveAG_41379340943598779362897656074, phi_thirtyFiveAG_41379340943598779362897656075, phi_thirtyFiveAG_41379340943598779362897656076,
    phi_thirtyFiveAG_41379340943598779362897656077, phi_thirtyFiveAG_41379340943598779362897656078, phi_thirtyFiveAG_41379340943598779362897656079,
    phi_thirtyFiveAG_41379340943598779362897656080, phi_thirtyFiveAG_41379340943598779362897656081, phi_thirtyFiveAG_41379340943598779362897656082,
    phi_thirtyFiveAG_41379340943598779362897656083, phi_thirtyFiveAG_41379340943598779362897656084, phi_thirtyFiveAG_41379340943598779362897656085,
    phi_thirtyFiveAG_41379340943598779362897656086, phi_thirtyFiveAG_41379340943598779362897656087, phi_thirtyFiveAG_41379340943598779362897656088,
    phi_thirtyFiveAG_41379340943598779362897656089, phi_thirtyFiveAG_41379340943598779362897656090, phi_thirtyFiveAG_41379340943598779362897656091,
    phi_thirtyFiveAG_41379340943598779362897656092, phi_thirtyFiveAG_41379340943598779362897656093, phi_thirtyFiveAG_41379340943598779362897656094,
    phi_thirtyFiveAG_41379340943598779362897656095, phi_thirtyFiveAG_41379340943598779362897656096, phi_thirtyFiveAG_41379340943598779362897656097,
    phi_thirtyFiveAG_41379340943598779362897656098]

end TotientTailPeriodKiller
end Erdos249257
