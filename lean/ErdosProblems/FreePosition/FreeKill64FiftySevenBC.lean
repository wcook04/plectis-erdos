import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 57P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftySevenBCFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftySevenBCFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftySevenBCFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftySevenBCFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftySevenBCFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftySevenBCFastPow a n * fiftySevenBCFastPow a n * a
        else fiftySevenBCFastPow a n * fiftySevenBCFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftySevenBC_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftySevenBC_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftySevenBC_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftySevenBC_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftySevenBC_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftySevenBC_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftySevenBC_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftySevenBC_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftySevenBC_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftySevenBC_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftySevenBC_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftySevenBC_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftySevenBC_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftySevenBC_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftySevenBC_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftySevenBC_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftySevenBC_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftySevenBC_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftySevenBC_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftySevenBC_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftySevenBC_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftySevenBC_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftySevenBC_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftySevenBC_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftySevenBC_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftySevenBC_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftySevenBC_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftySevenBC_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftySevenBC_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftySevenBC_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftySevenBC_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftySevenBC_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftySevenBC_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftySevenBC_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftySevenBC_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftySevenBC_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftySevenBC_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftySevenBC_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftySevenBC_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftySevenBC_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftySevenBC_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftySevenBC_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftySevenBC_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftySevenBC_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftySevenBC_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftySevenBC_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftySevenBC_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftySevenBC_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftySevenBC_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftySevenBC_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftySevenBC_257 : Nat.Prime 257 := by norm_num
private theorem prime_fiftySevenBC_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftySevenBC_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftySevenBC_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftySevenBC_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftySevenBC_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftySevenBC_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftySevenBC_317 : Nat.Prime 317 := by norm_num
private theorem prime_fiftySevenBC_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftySevenBC_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftySevenBC_349 : Nat.Prime 349 := by norm_num
private theorem prime_fiftySevenBC_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftySevenBC_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftySevenBC_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftySevenBC_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftySevenBC_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftySevenBC_409 : Nat.Prime 409 := by norm_num
private theorem prime_fiftySevenBC_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftySevenBC_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftySevenBC_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftySevenBC_457 : Nat.Prime 457 := by norm_num
private theorem prime_fiftySevenBC_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftySevenBC_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftySevenBC_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftySevenBC_491 : Nat.Prime 491 := by norm_num
private theorem prime_fiftySevenBC_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftySevenBC_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftySevenBC_563 : Nat.Prime 563 := by norm_num
private theorem prime_fiftySevenBC_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftySevenBC_587 : Nat.Prime 587 := by norm_num
private theorem prime_fiftySevenBC_593 : Nat.Prime 593 := by norm_num
private theorem prime_fiftySevenBC_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftySevenBC_607 : Nat.Prime 607 := by norm_num
private theorem prime_fiftySevenBC_613 : Nat.Prime 613 := by norm_num
private theorem prime_fiftySevenBC_617 : Nat.Prime 617 := by norm_num
private theorem prime_fiftySevenBC_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftySevenBC_643 : Nat.Prime 643 := by norm_num
private theorem prime_fiftySevenBC_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftySevenBC_673 : Nat.Prime 673 := by norm_num
private theorem prime_fiftySevenBC_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftySevenBC_701 : Nat.Prime 701 := by norm_num
private theorem prime_fiftySevenBC_727 : Nat.Prime 727 := by norm_num
private theorem prime_fiftySevenBC_739 : Nat.Prime 739 := by norm_num
private theorem prime_fiftySevenBC_743 : Nat.Prime 743 := by norm_num
private theorem prime_fiftySevenBC_751 : Nat.Prime 751 := by norm_num
private theorem prime_fiftySevenBC_757 : Nat.Prime 757 := by norm_num
private theorem prime_fiftySevenBC_797 : Nat.Prime 797 := by norm_num
private theorem prime_fiftySevenBC_809 : Nat.Prime 809 := by norm_num
private theorem prime_fiftySevenBC_821 : Nat.Prime 821 := by norm_num
private theorem prime_fiftySevenBC_823 : Nat.Prime 823 := by norm_num
private theorem prime_fiftySevenBC_827 : Nat.Prime 827 := by norm_num
private theorem prime_fiftySevenBC_839 : Nat.Prime 839 := by norm_num
private theorem prime_fiftySevenBC_857 : Nat.Prime 857 := by norm_num
private theorem prime_fiftySevenBC_881 : Nat.Prime 881 := by norm_num
private theorem prime_fiftySevenBC_887 : Nat.Prime 887 := by norm_num
private theorem prime_fiftySevenBC_907 : Nat.Prime 907 := by norm_num
private theorem prime_fiftySevenBC_919 : Nat.Prime 919 := by norm_num
private theorem prime_fiftySevenBC_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftySevenBC_983 : Nat.Prime 983 := by norm_num
private theorem prime_fiftySevenBC_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftySevenBC_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fiftySevenBC_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_fiftySevenBC_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fiftySevenBC_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fiftySevenBC_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fiftySevenBC_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fiftySevenBC_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_fiftySevenBC_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftySevenBC_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_fiftySevenBC_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fiftySevenBC_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fiftySevenBC_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fiftySevenBC_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftySevenBC_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_fiftySevenBC_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fiftySevenBC_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fiftySevenBC_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_fiftySevenBC_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_fiftySevenBC_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_fiftySevenBC_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_fiftySevenBC_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_fiftySevenBC_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fiftySevenBC_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_fiftySevenBC_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_fiftySevenBC_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_fiftySevenBC_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fiftySevenBC_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_fiftySevenBC_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_fiftySevenBC_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_fiftySevenBC_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_fiftySevenBC_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_fiftySevenBC_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_fiftySevenBC_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_fiftySevenBC_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_fiftySevenBC_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_fiftySevenBC_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_fiftySevenBC_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_fiftySevenBC_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_fiftySevenBC_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_fiftySevenBC_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_fiftySevenBC_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_fiftySevenBC_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_fiftySevenBC_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fiftySevenBC_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_fiftySevenBC_2459 : Nat.Prime 2459 := by norm_num
private theorem prime_fiftySevenBC_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_fiftySevenBC_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_fiftySevenBC_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_fiftySevenBC_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_fiftySevenBC_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_fiftySevenBC_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_fiftySevenBC_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_fiftySevenBC_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_fiftySevenBC_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_fiftySevenBC_3347 : Nat.Prime 3347 := by norm_num
private theorem prime_fiftySevenBC_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_fiftySevenBC_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_fiftySevenBC_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_fiftySevenBC_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_fiftySevenBC_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_fiftySevenBC_3701 : Nat.Prime 3701 := by norm_num
private theorem prime_fiftySevenBC_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_fiftySevenBC_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_fiftySevenBC_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_fiftySevenBC_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_fiftySevenBC_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_fiftySevenBC_4099 : Nat.Prime 4099 := by norm_num
private theorem prime_fiftySevenBC_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_fiftySevenBC_4201 : Nat.Prime 4201 := by norm_num
private theorem prime_fiftySevenBC_4253 : Nat.Prime 4253 := by norm_num
private theorem prime_fiftySevenBC_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_fiftySevenBC_4591 : Nat.Prime 4591 := by norm_num
private theorem prime_fiftySevenBC_4621 : Nat.Prime 4621 := by norm_num
private theorem prime_fiftySevenBC_4877 : Nat.Prime 4877 := by norm_num
private theorem prime_fiftySevenBC_4889 : Nat.Prime 4889 := by norm_num
private theorem prime_fiftySevenBC_5237 : Nat.Prime 5237 := by norm_num
private theorem prime_fiftySevenBC_5381 : Nat.Prime 5381 := by norm_num
private theorem prime_fiftySevenBC_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_fiftySevenBC_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_fiftySevenBC_5807 : Nat.Prime 5807 := by norm_num
private theorem prime_fiftySevenBC_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_fiftySevenBC_6653 : Nat.Prime 6653 := by norm_num
private theorem prime_fiftySevenBC_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_fiftySevenBC_6911 : Nat.Prime 6911 := by norm_num
private theorem prime_fiftySevenBC_7039 : Nat.Prime 7039 := by norm_num
private theorem prime_fiftySevenBC_7109 : Nat.Prime 7109 := by norm_num
private theorem prime_fiftySevenBC_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_fiftySevenBC_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_fiftySevenBC_7529 : Nat.Prime 7529 := by norm_num
private theorem prime_fiftySevenBC_7561 : Nat.Prime 7561 := by norm_num
private theorem prime_fiftySevenBC_7643 : Nat.Prime 7643 := by norm_num
private theorem prime_fiftySevenBC_8237 : Nat.Prime 8237 := by norm_num
private theorem prime_fiftySevenBC_8923 : Nat.Prime 8923 := by norm_num
private theorem prime_fiftySevenBC_8999 : Nat.Prime 8999 := by norm_num
private theorem prime_fiftySevenBC_9013 : Nat.Prime 9013 := by norm_num
private theorem prime_fiftySevenBC_9133 : Nat.Prime 9133 := by norm_num
private theorem prime_fiftySevenBC_9239 : Nat.Prime 9239 := by norm_num
private theorem prime_fiftySevenBC_9533 : Nat.Prime 9533 := by norm_num
private theorem prime_fiftySevenBC_10007 : Nat.Prime 10007 := by norm_num
private theorem prime_fiftySevenBC_11087 : Nat.Prime 11087 := by norm_num
private theorem prime_fiftySevenBC_11177 : Nat.Prime 11177 := by norm_num
private theorem prime_fiftySevenBC_11527 : Nat.Prime 11527 := by norm_num
private theorem prime_fiftySevenBC_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_fiftySevenBC_12451 : Nat.Prime 12451 := by norm_num
private theorem prime_fiftySevenBC_12541 : Nat.Prime 12541 := by norm_num
private theorem prime_fiftySevenBC_13147 : Nat.Prime 13147 := by norm_num
private theorem prime_fiftySevenBC_13229 : Nat.Prime 13229 := by norm_num
private theorem prime_fiftySevenBC_13291 : Nat.Prime 13291 := by norm_num
private theorem prime_fiftySevenBC_13669 : Nat.Prime 13669 := by norm_num
private theorem prime_fiftySevenBC_14081 : Nat.Prime 14081 := by norm_num
private theorem prime_fiftySevenBC_14407 : Nat.Prime 14407 := by norm_num
private theorem prime_fiftySevenBC_15139 : Nat.Prime 15139 := by norm_num
private theorem prime_fiftySevenBC_15731 : Nat.Prime 15731 := by norm_num
private theorem prime_fiftySevenBC_17669 : Nat.Prime 17669 := by norm_num
private theorem prime_fiftySevenBC_20107 : Nat.Prime 20107 := by norm_num
private theorem prime_fiftySevenBC_20399 : Nat.Prime 20399 := by norm_num
private theorem prime_fiftySevenBC_20551 : Nat.Prime 20551 := by norm_num
private theorem prime_fiftySevenBC_21121 : Nat.Prime 21121 := by norm_num
private theorem prime_fiftySevenBC_22571 : Nat.Prime 22571 := by norm_num
private theorem prime_fiftySevenBC_22741 : Nat.Prime 22741 := by norm_num
private theorem prime_fiftySevenBC_23167 : Nat.Prime 23167 := by norm_num
private theorem prime_fiftySevenBC_23311 : Nat.Prime 23311 := by norm_num
private theorem prime_fiftySevenBC_23399 : Nat.Prime 23399 := by norm_num
private theorem prime_fiftySevenBC_23677 : Nat.Prime 23677 := by norm_num
private theorem prime_fiftySevenBC_24029 : Nat.Prime 24029 := by norm_num
private theorem prime_fiftySevenBC_24043 : Nat.Prime 24043 := by norm_num
private theorem prime_fiftySevenBC_25561 : Nat.Prime 25561 := by norm_num
private theorem prime_fiftySevenBC_26863 : Nat.Prime 26863 := by norm_num
private theorem prime_fiftySevenBC_28631 : Nat.Prime 28631 := by norm_num
private theorem prime_fiftySevenBC_29123 : Nat.Prime 29123 := by norm_num
private theorem prime_fiftySevenBC_32369 : Nat.Prime 32369 := by norm_num
private theorem prime_fiftySevenBC_33589 : Nat.Prime 33589 := by norm_num
private theorem prime_fiftySevenBC_33637 : Nat.Prime 33637 := by norm_num
private theorem prime_fiftySevenBC_34369 : Nat.Prime 34369 := by norm_num
private theorem prime_fiftySevenBC_34607 : Nat.Prime 34607 := by norm_num
private theorem prime_fiftySevenBC_35977 : Nat.Prime 35977 := by norm_num
private theorem prime_fiftySevenBC_36191 : Nat.Prime 36191 := by norm_num
private theorem prime_fiftySevenBC_37117 : Nat.Prime 37117 := by norm_num
private theorem prime_fiftySevenBC_38261 : Nat.Prime 38261 := by norm_num
private theorem prime_fiftySevenBC_38723 : Nat.Prime 38723 := by norm_num
private theorem prime_fiftySevenBC_40193 : Nat.Prime 40193 := by norm_num
private theorem prime_fiftySevenBC_40841 : Nat.Prime 40841 := by norm_num
private theorem prime_fiftySevenBC_41077 : Nat.Prime 41077 := by norm_num
private theorem prime_fiftySevenBC_42391 : Nat.Prime 42391 := by norm_num
private theorem prime_fiftySevenBC_43237 : Nat.Prime 43237 := by norm_num
private theorem prime_fiftySevenBC_46477 : Nat.Prime 46477 := by norm_num
private theorem prime_fiftySevenBC_47777 : Nat.Prime 47777 := by norm_num
private theorem prime_fiftySevenBC_49633 : Nat.Prime 49633 := by norm_num
private theorem prime_fiftySevenBC_50033 : Nat.Prime 50033 := by norm_num
private theorem prime_fiftySevenBC_51829 : Nat.Prime 51829 := by norm_num
private theorem prime_fiftySevenBC_52249 : Nat.Prime 52249 := by norm_num
private theorem prime_fiftySevenBC_53161 : Nat.Prime 53161 := by norm_num
private theorem prime_fiftySevenBC_55661 : Nat.Prime 55661 := by norm_num
private theorem prime_fiftySevenBC_56731 : Nat.Prime 56731 := by norm_num
private theorem prime_fiftySevenBC_57653 : Nat.Prime 57653 := by norm_num
private theorem prime_fiftySevenBC_57787 : Nat.Prime 57787 := by norm_num
private theorem prime_fiftySevenBC_58363 : Nat.Prime 58363 := by norm_num
private theorem prime_fiftySevenBC_63389 : Nat.Prime 63389 := by norm_num
private theorem prime_fiftySevenBC_65563 : Nat.Prime 65563 := by norm_num
private theorem prime_fiftySevenBC_68539 : Nat.Prime 68539 := by norm_num
private theorem prime_fiftySevenBC_69109 : Nat.Prime 69109 := by norm_num
private theorem prime_fiftySevenBC_69341 : Nat.Prime 69341 := by norm_num
private theorem prime_fiftySevenBC_70901 : Nat.Prime 70901 := by norm_num
private theorem prime_fiftySevenBC_71633 : Nat.Prime 71633 := by norm_num
private theorem prime_fiftySevenBC_74311 : Nat.Prime 74311 := by norm_num
private theorem prime_fiftySevenBC_75389 : Nat.Prime 75389 := by norm_num
private theorem prime_fiftySevenBC_75653 : Nat.Prime 75653 := by norm_num
private theorem prime_fiftySevenBC_80407 : Nat.Prime 80407 := by norm_num
private theorem prime_fiftySevenBC_83137 : Nat.Prime 83137 := by norm_num
private theorem prime_fiftySevenBC_87679 : Nat.Prime 87679 := by norm_num
private theorem prime_fiftySevenBC_87887 : Nat.Prime 87887 := by norm_num
private theorem prime_fiftySevenBC_89083 : Nat.Prime 89083 := by norm_num
private theorem prime_fiftySevenBC_96557 : Nat.Prime 96557 := by norm_num
private theorem prime_fiftySevenBC_120871 : Nat.Prime 120871 := by norm_num
private theorem prime_fiftySevenBC_121787 : Nat.Prime 121787 := by norm_num
private theorem prime_fiftySevenBC_128903 : Nat.Prime 128903 := by norm_num
private theorem prime_fiftySevenBC_143281 : Nat.Prime 143281 := by norm_num
private theorem prime_fiftySevenBC_146807 : Nat.Prime 146807 := by norm_num
private theorem prime_fiftySevenBC_149909 : Nat.Prime 149909 := by norm_num
private theorem prime_fiftySevenBC_154417 : Nat.Prime 154417 := by norm_num
private theorem prime_fiftySevenBC_155167 : Nat.Prime 155167 := by norm_num
private theorem prime_fiftySevenBC_158129 : Nat.Prime 158129 := by norm_num
private theorem prime_fiftySevenBC_162343 : Nat.Prime 162343 := by norm_num
private theorem prime_fiftySevenBC_165331 : Nat.Prime 165331 := by norm_num
private theorem prime_fiftySevenBC_179563 : Nat.Prime 179563 := by norm_num
private theorem prime_fiftySevenBC_188653 : Nat.Prime 188653 := by norm_num
private theorem prime_fiftySevenBC_201247 : Nat.Prime 201247 := by norm_num
private theorem prime_fiftySevenBC_205213 : Nat.Prime 205213 := by norm_num
private theorem prime_fiftySevenBC_211859 : Nat.Prime 211859 := by norm_num
private theorem prime_fiftySevenBC_215471 : Nat.Prime 215471 := by norm_num
private theorem prime_fiftySevenBC_221281 : Nat.Prime 221281 := by norm_num
private theorem prime_fiftySevenBC_223481 : Nat.Prime 223481 := by norm_num
private theorem prime_fiftySevenBC_224443 : Nat.Prime 224443 := by norm_num
private theorem prime_fiftySevenBC_229727 : Nat.Prime 229727 := by norm_num
private theorem prime_fiftySevenBC_232871 : Nat.Prime 232871 := by norm_num
private theorem prime_fiftySevenBC_240209 : Nat.Prime 240209 := by norm_num
private theorem prime_fiftySevenBC_255841 : Nat.Prime 255841 := by norm_num
private theorem prime_fiftySevenBC_258551 : Nat.Prime 258551 := by norm_num
private theorem prime_fiftySevenBC_258847 : Nat.Prime 258847 := by norm_num
private theorem prime_fiftySevenBC_272759 : Nat.Prime 272759 := by norm_num
private theorem prime_fiftySevenBC_277007 : Nat.Prime 277007 := by norm_num
private theorem prime_fiftySevenBC_278393 : Nat.Prime 278393 := by norm_num
private theorem prime_fiftySevenBC_280037 : Nat.Prime 280037 := by norm_num
private theorem prime_fiftySevenBC_293413 : Nat.Prime 293413 := by norm_num
private theorem prime_fiftySevenBC_296377 : Nat.Prime 296377 := by norm_num
private theorem prime_fiftySevenBC_307589 : Nat.Prime 307589 := by norm_num
private theorem prime_fiftySevenBC_316907 : Nat.Prime 316907 := by norm_num
private theorem prime_fiftySevenBC_322111 : Nat.Prime 322111 := by norm_num
private theorem prime_fiftySevenBC_324733 : Nat.Prime 324733 := by norm_num
private theorem prime_fiftySevenBC_325877 : Nat.Prime 325877 := by norm_num
private theorem prime_fiftySevenBC_332933 : Nat.Prime 332933 := by norm_num
private theorem prime_fiftySevenBC_339761 : Nat.Prime 339761 := by norm_num
private theorem prime_fiftySevenBC_355513 : Nat.Prime 355513 := by norm_num
private theorem prime_fiftySevenBC_382661 : Nat.Prime 382661 := by norm_num
private theorem prime_fiftySevenBC_388067 : Nat.Prime 388067 := by norm_num
private theorem prime_fiftySevenBC_423179 : Nat.Prime 423179 := by norm_num
private theorem prime_fiftySevenBC_428801 : Nat.Prime 428801 := by norm_num
private theorem prime_fiftySevenBC_435143 : Nat.Prime 435143 := by norm_num
private theorem prime_fiftySevenBC_461171 : Nat.Prime 461171 := by norm_num
private theorem prime_fiftySevenBC_495617 : Nat.Prime 495617 := by norm_num
private theorem prime_fiftySevenBC_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_fiftySevenBC_513319 : Nat.Prime 513319 := by norm_num
private theorem prime_fiftySevenBC_545483 : Nat.Prime 545483 := by norm_num
private theorem prime_fiftySevenBC_563039 : Nat.Prime 563039 := by norm_num
private theorem prime_fiftySevenBC_597263 : Nat.Prime 597263 := by norm_num
private theorem prime_fiftySevenBC_611467 : Nat.Prime 611467 := by norm_num
private theorem prime_fiftySevenBC_627947 : Nat.Prime 627947 := by norm_num
private theorem prime_fiftySevenBC_660337 : Nat.Prime 660337 := by norm_num
private theorem prime_fiftySevenBC_693283 : Nat.Prime 693283 := by norm_num
private theorem prime_fiftySevenBC_752929 : Nat.Prime 752929 := by norm_num
private theorem prime_fiftySevenBC_792371 : Nat.Prime 792371 := by norm_num
private theorem prime_fiftySevenBC_806543 : Nat.Prime 806543 := by norm_num
private theorem prime_fiftySevenBC_812689 : Nat.Prime 812689 := by norm_num
private theorem prime_fiftySevenBC_817331 : Nat.Prime 817331 := by norm_num
private theorem prime_fiftySevenBC_832159 : Nat.Prime 832159 := by norm_num
private theorem prime_fiftySevenBC_837773 : Nat.Prime 837773 := by norm_num
private theorem prime_fiftySevenBC_843043 : Nat.Prime 843043 := by norm_num
private theorem prime_fiftySevenBC_880133 : Nat.Prime 880133 := by norm_num
private theorem prime_fiftySevenBC_886799 : Nat.Prime 886799 := by norm_num
private theorem prime_fiftySevenBC_1044437 : Nat.Prime 1044437 := by norm_num
private theorem prime_fiftySevenBC_1072387 : Nat.Prime 1072387 := by norm_num
private theorem prime_fiftySevenBC_1141597 : Nat.Prime 1141597 := by norm_num
private theorem prime_fiftySevenBC_1179551 : Nat.Prime 1179551 := by norm_num
private theorem prime_fiftySevenBC_1236307 : Nat.Prime 1236307 := by norm_num
private theorem prime_fiftySevenBC_1261487 : Nat.Prime 1261487 := by norm_num
private theorem prime_fiftySevenBC_1283701 : Nat.Prime 1283701 := by norm_num
private theorem prime_fiftySevenBC_1284551 : Nat.Prime 1284551 := by norm_num
private theorem prime_fiftySevenBC_1372363 : Nat.Prime 1372363 := by norm_num
private theorem prime_fiftySevenBC_1394989 : Nat.Prime 1394989 := by norm_num
private theorem prime_fiftySevenBC_1498309 : Nat.Prime 1498309 := by norm_num
private theorem prime_fiftySevenBC_1505183 : Nat.Prime 1505183 := by norm_num
private theorem prime_fiftySevenBC_1531447 : Nat.Prime 1531447 := by norm_num
private theorem prime_fiftySevenBC_1686491 : Nat.Prime 1686491 := by norm_num
private theorem prime_fiftySevenBC_1696883 : Nat.Prime 1696883 := by norm_num
private theorem prime_fiftySevenBC_1726787 : Nat.Prime 1726787 := by norm_num
private theorem prime_fiftySevenBC_1735673 : Nat.Prime 1735673 := by norm_num
private theorem prime_fiftySevenBC_1747723 : Nat.Prime 1747723 := by norm_num
private theorem prime_fiftySevenBC_1806703 : Nat.Prime 1806703 := by norm_num
private theorem prime_fiftySevenBC_1931773 : Nat.Prime 1931773 := by norm_num
private theorem prime_fiftySevenBC_1940597 : Nat.Prime 1940597 := by norm_num
private theorem prime_fiftySevenBC_2004007 : Nat.Prime 2004007 := by norm_num
private theorem prime_fiftySevenBC_2011573 : Nat.Prime 2011573 := by norm_num
private theorem prime_fiftySevenBC_2020243 : Nat.Prime 2020243 := by norm_num
private theorem prime_fiftySevenBC_2092919 : Nat.Prime 2092919 := by norm_num
private theorem prime_fiftySevenBC_2094601 : Nat.Prime 2094601 := by norm_num
private theorem prime_fiftySevenBC_2106173 : Nat.Prime 2106173 := by norm_num
private theorem prime_fiftySevenBC_2160841 : Nat.Prime 2160841 := by norm_num
private theorem prime_fiftySevenBC_2162059 : Nat.Prime 2162059 := by norm_num
private theorem prime_fiftySevenBC_2221031 : Nat.Prime 2221031 := by norm_num
private theorem prime_fiftySevenBC_2644573 : Nat.Prime 2644573 := by norm_num
private theorem prime_fiftySevenBC_2772529 : Nat.Prime 2772529 := by norm_num
private theorem prime_fiftySevenBC_2801317 : Nat.Prime 2801317 := by norm_num
private theorem prime_fiftySevenBC_2857507 : Nat.Prime 2857507 := by norm_num
private theorem prime_fiftySevenBC_2938361 : Nat.Prime 2938361 := by norm_num
private theorem prime_fiftySevenBC_3007747 : Nat.Prime 3007747 := by norm_num
private theorem prime_fiftySevenBC_3033971 : Nat.Prime 3033971 := by norm_num
private theorem prime_fiftySevenBC_3272323 : Nat.Prime 3272323 := by norm_num
private theorem prime_fiftySevenBC_3288611 : Nat.Prime 3288611 := by norm_num
private theorem prime_fiftySevenBC_3290377 : Nat.Prime 3290377 := by norm_num
private theorem prime_fiftySevenBC_3763027 : Nat.Prime 3763027 := by norm_num
private theorem prime_fiftySevenBC_4026277 : Nat.Prime 4026277 := by norm_num
private theorem prime_fiftySevenBC_4314803 : Nat.Prime 4314803 := by norm_num
private theorem prime_fiftySevenBC_4497817 : Nat.Prime 4497817 := by norm_num
private theorem prime_fiftySevenBC_4900517 : Nat.Prime 4900517 := by norm_num
private theorem prime_fiftySevenBC_5424233 : Nat.Prime 5424233 := by norm_num
private theorem prime_fiftySevenBC_5530571 : Nat.Prime 5530571 := by norm_num
private theorem prime_fiftySevenBC_5918687 : Nat.Prime 5918687 := by norm_num
private theorem prime_fiftySevenBC_6336409 : Nat.Prime 6336409 := by norm_num
private theorem prime_fiftySevenBC_7300459 : Nat.Prime 7300459 := by norm_num
private theorem prime_fiftySevenBC_7342799 : Nat.Prime 7342799 := by norm_num
private theorem prime_fiftySevenBC_7501433 : Nat.Prime 7501433 := by norm_num
private theorem prime_fiftySevenBC_8372321 : Nat.Prime 8372321 := by norm_num
private theorem prime_fiftySevenBC_8434913 : Nat.Prime 8434913 := by norm_num
private theorem prime_fiftySevenBC_9758599 : Nat.Prime 9758599 := by norm_num
private theorem prime_fiftySevenBC_10159477 : Nat.Prime 10159477 := by norm_num
private theorem prime_fiftySevenBC_11880919 : Nat.Prime 11880919 := by norm_num
private theorem prime_fiftySevenBC_12042619 : Nat.Prime 12042619 := by norm_num
private theorem prime_fiftySevenBC_12390029 : Nat.Prime 12390029 := by norm_num
private theorem prime_fiftySevenBC_12492211 : Nat.Prime 12492211 := by norm_num
private theorem prime_fiftySevenBC_14418251 : Nat.Prime 14418251 := by norm_num
private theorem prime_fiftySevenBC_15219067 : Nat.Prime 15219067 := by norm_num
private theorem prime_fiftySevenBC_15875137 : Nat.Prime 15875137 := by norm_num
private theorem prime_fiftySevenBC_16063259 : Nat.Prime 16063259 := by norm_num
private theorem prime_fiftySevenBC_16428319 : Nat.Prime 16428319 := by norm_num
private theorem prime_fiftySevenBC_16587401 : Nat.Prime 16587401 := by norm_num
private theorem prime_fiftySevenBC_16714199 : Nat.Prime 16714199 := by norm_num
private theorem prime_fiftySevenBC_16767547 : Nat.Prime 16767547 := by norm_num
private theorem prime_fiftySevenBC_17110777 : Nat.Prime 17110777 := by norm_num
private theorem prime_fiftySevenBC_17543723 : Nat.Prime 17543723 := by norm_num
private theorem prime_fiftySevenBC_17593703 : Nat.Prime 17593703 := by norm_num
private theorem prime_fiftySevenBC_17838031 : Nat.Prime 17838031 := by norm_num
private theorem prime_fiftySevenBC_19773401 : Nat.Prime 19773401 := by norm_num
private theorem prime_fiftySevenBC_19775887 : Nat.Prime 19775887 := by norm_num
private theorem prime_fiftySevenBC_19839689 : Nat.Prime 19839689 := by norm_num
private theorem prime_fiftySevenBC_23557913 : Nat.Prime 23557913 := by norm_num
private theorem prime_fiftySevenBC_24656131 : Nat.Prime 24656131 := by norm_num
private theorem prime_fiftySevenBC_27087023 : Nat.Prime 27087023 := by norm_num
private theorem prime_fiftySevenBC_28034593 : Nat.Prime 28034593 := by norm_num
private theorem prime_fiftySevenBC_29036411 : Nat.Prime 29036411 := by norm_num
private theorem prime_fiftySevenBC_29776049 : Nat.Prime 29776049 := by norm_num

private theorem prime_fiftySevenBC_30186323 : Nat.Prime 30186323 := by
  apply lucas_primality 30186323 (2 : ZMod 30186323)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (229, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (229, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) = 30186323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_229
      · exact prime_fiftySevenBC_3877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30186323) ^ 15093161 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30186323) ^ 1775666 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30186323) ^ 131818 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30186323) ^ 7786 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_30498877 : Nat.Prime 30498877 := by
  apply lucas_primality 30498877 (5 : ZMod 30498877)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (89, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (89, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 30498877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_89
      · exact prime_fiftySevenBC_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30498877) ^ 15249438 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30498877) ^ 10166292 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30498877) ^ 1605204 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30498877) ^ 342684 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30498877) ^ 182628 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_31290443 : Nat.Prime 31290443 := by
  apply lucas_primality 31290443 (2 : ZMod 31290443)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (89, 1), (7643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (89, 1), (7643, 1)] : List FactorBlock).map factorBlockValue).prod) = 31290443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_89
      · exact prime_fiftySevenBC_7643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31290443) ^ 15645221 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290443) ^ 1360454 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290443) ^ 351578 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31290443) ^ 4094 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_31816201 : Nat.Prime 31816201 := by
  apply lucas_primality 31816201 (11 : ZMod 31816201)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (13, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (13, 1), (4079, 1)] : List FactorBlock).map factorBlockValue).prod) = 31816201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_4079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 31816201) ^ 15908100 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 31816201) ^ 10605400 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 31816201) ^ 6363240 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 31816201) ^ 2447400 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 31816201) ^ 7800 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_33559817 : Nat.Prime 33559817 := by
  apply lucas_primality 33559817 (3 : ZMod 33559817)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (607, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (607, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) = 33559817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_607
      · exact prime_fiftySevenBC_6911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33559817) ^ 16779908 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559817) ^ 55288 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559817) ^ 4856 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_35738317 : Nat.Prime 35738317 := by
  apply lucas_primality 35738317 (2 : ZMod 35738317)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (52249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (52249, 1)] : List FactorBlock).map factorBlockValue).prod) = 35738317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_52249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35738317) ^ 17869158 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 35738317) ^ 11912772 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 35738317) ^ 1880964 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 35738317) ^ 684 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_42708037 : Nat.Prime 42708037 := by
  apply lucas_primality 42708037 (2 : ZMod 42708037)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 2), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 2), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 42708037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42708037) ^ 21354018 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42708037) ^ 14236012 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42708037) ^ 6101148 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42708037) ^ 805812 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42708037) ^ 235956 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_45273589 : Nat.Prime 45273589 := by
  apply lucas_primality 45273589 (2 : ZMod 45273589)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (42391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (42391, 1)] : List FactorBlock).map factorBlockValue).prod) = 45273589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_89
      · exact prime_fiftySevenBC_42391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45273589) ^ 22636794 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 45273589) ^ 15091196 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 45273589) ^ 508692 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 45273589) ^ 1068 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_48009943 : Nat.Prime 48009943 := by
  apply lucas_primality 48009943 (3 : ZMod 48009943)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (24029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (24029, 1)] : List FactorBlock).map factorBlockValue).prod) = 48009943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_24029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48009943) ^ 24004971 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48009943) ^ 16003314 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48009943) ^ 1297566 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48009943) ^ 1998 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_48180019 : Nat.Prime 48180019 := by
  apply lucas_primality 48180019 (3 : ZMod 48180019)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (13229, 1)] : List FactorBlock).map factorBlockValue).prod) = 48180019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_607
      · exact prime_fiftySevenBC_13229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48180019) ^ 24090009 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48180019) ^ 16060006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48180019) ^ 79374 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 48180019) ^ 3642 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_51492151 : Nat.Prime 51492151 := by
  apply lucas_primality 51492151 (7 : ZMod 51492151)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 51492151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51492151) ^ 25746075 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51492151) ^ 17164050 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51492151) ^ 10298430 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51492151) ^ 3028950 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51492151) ^ 971550 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51492151) ^ 405450 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_52875133 : Nat.Prime 52875133 := by
  apply lucas_primality 52875133 (5 : ZMod 52875133)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (83137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (83137, 1)] : List FactorBlock).map factorBlockValue).prod) = 52875133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_83137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52875133) ^ 26437566 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52875133) ^ 17625044 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52875133) ^ 997644 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52875133) ^ 636 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_56284999 : Nat.Prime 56284999 := by
  apply lucas_primality 56284999 (3 : ZMod 56284999)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) = 56284999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_4201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56284999) ^ 28142499 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56284999) ^ 18761666 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56284999) ^ 8040714 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56284999) ^ 5116818 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56284999) ^ 1940862 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 56284999) ^ 13398 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_70798187 : Nat.Prime 70798187 := by
  apply lucas_primality 70798187 (2 : ZMod 70798187)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (61, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (61, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 70798187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70798187) ^ 35399093 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70798187) ^ 3078182 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70798187) ^ 1160626 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70798187) ^ 64538 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_82108777 : Nat.Prime 82108777 := by
  apply lucas_primality 82108777 (5 : ZMod 82108777)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (201247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (201247, 1)] : List FactorBlock).map factorBlockValue).prod) = 82108777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_201247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 82108777) ^ 41054388 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 82108777) ^ 27369592 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 82108777) ^ 4829928 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 82108777) ^ 408 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_88445191 : Nat.Prime 88445191 := by
  apply lucas_primality 88445191 (3 : ZMod 88445191)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (155167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (155167, 1)] : List FactorBlock).map factorBlockValue).prod) = 88445191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_155167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88445191) ^ 44222595 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 88445191) ^ 29481730 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 88445191) ^ 17689038 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 88445191) ^ 4655010 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 88445191) ^ 570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_94854233 : Nat.Prime 94854233 := by
  apply lucas_primality 94854233 (3 : ZMod 94854233)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (56731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (56731, 1)] : List FactorBlock).map factorBlockValue).prod) = 94854233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_56731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94854233) ^ 47427116 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 94854233) ^ 8623112 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 94854233) ^ 4992328 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 94854233) ^ 1672 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_97115377 : Nat.Prime 97115377 := by
  apply lucas_primality 97115377 (5 : ZMod 97115377)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (89, 1), (127, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (89, 1), (127, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 97115377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_89
      · exact prime_fiftySevenBC_127
      · exact prime_fiftySevenBC_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97115377) ^ 48557688 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97115377) ^ 32371792 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97115377) ^ 1091184 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97115377) ^ 764688 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97115377) ^ 542544 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_98216413 : Nat.Prime 98216413 := by
  apply lucas_primality 98216413 (6 : ZMod 98216413)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (109, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (109, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 98216413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_109
      · exact prime_fiftySevenBC_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98216413) ^ 49108206 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 98216413) ^ 32738804 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 98216413) ^ 14030916 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 98216413) ^ 5777436 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 98216413) ^ 901068 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 98216413) ^ 155652 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_102667717 : Nat.Prime 102667717 := by
  apply lucas_primality 102667717 (5 : ZMod 102667717)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (50033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (50033, 1)] : List FactorBlock).map factorBlockValue).prod) = 102667717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_50033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102667717) ^ 51333858 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 102667717) ^ 34222572 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 102667717) ^ 5403564 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 102667717) ^ 2052 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_137322883 : Nat.Prime 137322883 := by
  apply lucas_primality 137322883 (2 : ZMod 137322883)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1009, 1), (7561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1009, 1), (7561, 1)] : List FactorBlock).map factorBlockValue).prod) = 137322883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_1009
      · exact prime_fiftySevenBC_7561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 137322883) ^ 68661441 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 137322883) ^ 45774294 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 137322883) ^ 136098 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 137322883) ^ 18162 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_143194283 : Nat.Prime 143194283 := by
  apply lucas_primality 143194283 (2 : ZMod 143194283)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (727, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (727, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 143194283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_727
      · exact prime_fiftySevenBC_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 143194283) ^ 71597141 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143194283) ^ 20456326 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143194283) ^ 13017662 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143194283) ^ 196966 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143194283) ^ 111958 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_143604179 : Nat.Prime 143604179 := by
  apply lucas_primality 143604179 (2 : ZMod 143604179)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1940597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1940597, 1)] : List FactorBlock).map factorBlockValue).prod) = 143604179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_1940597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143604179) ^ 71802089 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143604179) ^ 3881194 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 143604179) ^ 74 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_154680373 : Nat.Prime 154680373 := by
  apply lucas_primality 154680373 (2 : ZMod 154680373)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (41, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (41, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) = 154680373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_41
      · exact prime_fiftySevenBC_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154680373) ^ 77340186 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 154680373) ^ 51560124 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 154680373) ^ 22097196 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 154680373) ^ 14061852 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 154680373) ^ 3772692 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 154680373) ^ 113652 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_163768879 : Nat.Prime 163768879 := by
  apply lucas_primality 163768879 (15 : ZMod 163768879)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 2), (13, 1), (23, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 2), (13, 1), (23, 2)] : List FactorBlock).map factorBlockValue).prod) = 163768879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 163768879) ^ 81884439 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 163768879) ^ 54589626 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 163768879) ^ 23395554 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 163768879) ^ 12597606 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 163768879) ^ 7120386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_183419633 : Nat.Prime 183419633 := by
  apply lucas_primality 183419633 (3 : ZMod 183419633)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (227, 1), (4591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (227, 1), (4591, 1)] : List FactorBlock).map factorBlockValue).prod) = 183419633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_227
      · exact prime_fiftySevenBC_4591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 183419633) ^ 91709816 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 183419633) ^ 16674512 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 183419633) ^ 808016 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 183419633) ^ 39952 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_199610237 : Nat.Prime 199610237 := by
  apply lucas_primality 199610237 (2 : ZMod 199610237)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2293, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2293, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 199610237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_2293
      · exact prime_fiftySevenBC_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 199610237) ^ 99805118 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 199610237) ^ 28515748 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 199610237) ^ 87052 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 199610237) ^ 64204 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_251641417 : Nat.Prime 251641417 := by
  apply lucas_primality 251641417 (5 : ZMod 251641417)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (806543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (806543, 1)] : List FactorBlock).map factorBlockValue).prod) = 251641417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_806543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 251641417) ^ 125820708 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 251641417) ^ 83880472 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 251641417) ^ 19357032 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 251641417) ^ 312 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_253932841 : Nat.Prime 253932841 := by
  apply lucas_primality 253932841 (11 : ZMod 253932841)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (33589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (33589, 1)] : List FactorBlock).map factorBlockValue).prod) = 253932841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_33589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 253932841) ^ 126966420 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 253932841) ^ 84644280 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 253932841) ^ 50786568 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 253932841) ^ 36276120 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 253932841) ^ 7560 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_296076787 : Nat.Prime 296076787 := by
  apply lucas_primality 296076787 (2 : ZMod 296076787)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (163, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (163, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) = 296076787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_163
      · exact prime_fiftySevenBC_3121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 296076787) ^ 148038393 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 296076787) ^ 98692262 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 296076787) ^ 3052338 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 296076787) ^ 1816422 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 296076787) ^ 94866 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_308952907 : Nat.Prime 308952907 := by
  apply lucas_primality 308952907 (7 : ZMod 308952907)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (51492151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (51492151, 1)] : List FactorBlock).map factorBlockValue).prod) = 308952907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_51492151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 308952907) ^ 154476453 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 308952907) ^ 102984302 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 308952907) ^ 6 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_318148199 : Nat.Prime 318148199 := by
  apply lucas_primality 318148199 (13 : ZMod 318148199)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (8372321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (8372321, 1)] : List FactorBlock).map factorBlockValue).prod) = 318148199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_8372321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 318148199) ^ 159074099 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 318148199) ^ 16744642 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 318148199) ^ 38 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_318283949 : Nat.Prime 318283949 := by
  apply lucas_primality 318283949 (2 : ZMod 318283949)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239, 1), (332933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239, 1), (332933, 1)] : List FactorBlock).map factorBlockValue).prod) = 318283949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_239
      · exact prime_fiftySevenBC_332933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 318283949) ^ 159141974 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 318283949) ^ 1331732 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 318283949) ^ 956 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_325044277 : Nat.Prime 325044277 := by
  apply lucas_primality 325044277 (2 : ZMod 325044277)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (27087023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (27087023, 1)] : List FactorBlock).map factorBlockValue).prod) = 325044277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_27087023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 325044277) ^ 162522138 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 325044277) ^ 108348092 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 325044277) ^ 12 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_331139989 : Nat.Prime 331139989 := by
  apply lucas_primality 331139989 (6 : ZMod 331139989)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (461, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (461, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 331139989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_461
      · exact prime_fiftySevenBC_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 331139989) ^ 165569994 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 331139989) ^ 110379996 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 331139989) ^ 718308 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 331139989) ^ 448092 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_335172443 : Nat.Prime 335172443 := by
  apply lucas_primality 335172443 (2 : ZMod 335172443)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (97, 1), (9239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (97, 1), (9239, 1)] : List FactorBlock).map factorBlockValue).prod) = 335172443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_9239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 335172443) ^ 167586221 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335172443) ^ 30470222 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335172443) ^ 19716026 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335172443) ^ 3455386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335172443) ^ 36278 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_366839267 : Nat.Prime 366839267 := by
  apply lucas_primality 366839267 (2 : ZMod 366839267)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (183419633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (183419633, 1)] : List FactorBlock).map factorBlockValue).prod) = 366839267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_183419633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 366839267) ^ 183419633 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 366839267) ^ 2 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_371136173 : Nat.Prime 371136173 := by
  apply lucas_primality 371136173 (2 : ZMod 371136173)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (8434913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (8434913, 1)] : List FactorBlock).map factorBlockValue).prod) = 371136173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_8434913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 371136173) ^ 185568086 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 371136173) ^ 33739652 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 371136173) ^ 44 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_375903491 : Nat.Prime 375903491 := by
  apply lucas_primality 375903491 (6 : ZMod 375903491)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (127, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (127, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 375903491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_127
      · exact prime_fiftySevenBC_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 375903491) ^ 187951745 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 375903491) ^ 75180698 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 375903491) ^ 22111970 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 375903491) ^ 16343630 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 375903491) ^ 2959870 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 375903491) ^ 496570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_383427283 : Nat.Prime 383427283 := by
  apply lucas_primality 383427283 (2 : ZMod 383427283)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 2), (31, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 2), (31, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 383427283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_31
      · exact prime_fiftySevenBC_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 383427283) ^ 191713641 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 383427283) ^ 127809094 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 383427283) ^ 54775326 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 383427283) ^ 22554546 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 383427283) ^ 12368622 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 383427283) ^ 376278 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_422255347 : Nat.Prime 422255347 := by
  apply lucas_primality 422255347 (2 : ZMod 422255347)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (101, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (101, 1), (13147, 1)] : List FactorBlock).map factorBlockValue).prod) = 422255347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_13147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 422255347) ^ 211127673 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 422255347) ^ 140751782 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 422255347) ^ 7967082 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 422255347) ^ 4180746 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 422255347) ^ 32118 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_582692263 : Nat.Prime 582692263 := by
  apply lucas_primality 582692263 (3 : ZMod 582692263)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97115377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97115377, 1)] : List FactorBlock).map factorBlockValue).prod) = 582692263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_97115377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 582692263) ^ 291346131 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 582692263) ^ 194230754 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 582692263) ^ 6 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_656122319 : Nat.Prime 656122319 := by
  apply lucas_primality 656122319 (13 : ZMod 656122319)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (491, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (491, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) = 656122319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_137
      · exact prime_fiftySevenBC_491
      · exact prime_fiftySevenBC_4877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 656122319) ^ 328061159 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 656122319) ^ 4789214 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 656122319) ^ 1336298 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 656122319) ^ 134534 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_731842651 : Nat.Prime 731842651 := by
  apply lucas_primality 731842651 (2 : ZMod 731842651)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (21121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (11, 1), (21121, 1)] : List FactorBlock).map factorBlockValue).prod) = 731842651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_21121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 731842651) ^ 365921325 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 731842651) ^ 243947550 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 731842651) ^ 146368530 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 731842651) ^ 104548950 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 731842651) ^ 66531150 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 731842651) ^ 34650 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_778079567 : Nat.Prime 778079567 := by
  apply lucas_primality 778079567 (5 : ZMod 778079567)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1471, 1), (24043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1471, 1), (24043, 1)] : List FactorBlock).map factorBlockValue).prod) = 778079567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_1471
      · exact prime_fiftySevenBC_24043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 778079567) ^ 389039783 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 778079567) ^ 70734506 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 778079567) ^ 528946 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 778079567) ^ 32362 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_857719609 : Nat.Prime 857719609 := by
  apply lucas_primality 857719609 (7 : ZMod 857719609)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (35738317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (35738317, 1)] : List FactorBlock).map factorBlockValue).prod) = 857719609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_35738317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 857719609) ^ 428859804 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 857719609) ^ 285906536 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 857719609) ^ 24 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_867240343 : Nat.Prime 867240343 := by
  apply lucas_primality 867240343 (5 : ZMod 867240343)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (48180019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (48180019, 1)] : List FactorBlock).map factorBlockValue).prod) = 867240343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_48180019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 867240343) ^ 433620171 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 867240343) ^ 289080114 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 867240343) ^ 18 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_869270081 : Nat.Prime 869270081 := by
  apply lucas_primality 869270081 (3 : ZMod 869270081)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (388067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (388067, 1)] : List FactorBlock).map factorBlockValue).prod) = 869270081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_388067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 869270081) ^ 434635040 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 869270081) ^ 173854016 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 869270081) ^ 124181440 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 869270081) ^ 2240 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_912840689 : Nat.Prime 912840689 := by
  apply lucas_primality 912840689 (3 : ZMod 912840689)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (223, 1), (255841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (223, 1), (255841, 1)] : List FactorBlock).map factorBlockValue).prod) = 912840689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_223
      · exact prime_fiftySevenBC_255841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 912840689) ^ 456420344 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 912840689) ^ 4093456 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 912840689) ^ 3568 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_988621559 : Nat.Prime 988621559 := by
  apply lucas_primality 988621559 (7 : ZMod 988621559)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (693283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (693283, 1)] : List FactorBlock).map factorBlockValue).prod) = 988621559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_31
      · exact prime_fiftySevenBC_693283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 988621559) ^ 494310779 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 988621559) ^ 42983546 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 988621559) ^ 31891018 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 988621559) ^ 1426 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1006794511 : Nat.Prime 1006794511 := by
  apply lucas_primality 1006794511 (3 : ZMod 1006794511)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (33559817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (33559817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006794511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_33559817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1006794511) ^ 503397255 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006794511) ^ 335598170 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006794511) ^ 201358902 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1006794511) ^ 30 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1060723231 : Nat.Prime 1060723231 := by
  apply lucas_primality 1060723231 (3 : ZMod 1060723231)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (67, 1), (75389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (67, 1), (75389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1060723231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_67
      · exact prime_fiftySevenBC_75389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1060723231) ^ 530361615 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060723231) ^ 353574410 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060723231) ^ 212144646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060723231) ^ 151531890 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060723231) ^ 15831690 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060723231) ^ 14070 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1428457609 : Nat.Prime 1428457609 := by
  apply lucas_primality 1428457609 (7 : ZMod 1428457609)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19839689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19839689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1428457609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_19839689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1428457609) ^ 714228804 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1428457609) ^ 476152536 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1428457609) ^ 72 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1553145493 : Nat.Prime 1553145493 := by
  apply lucas_primality 1553145493 (5 : ZMod 1553145493)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (1931773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (1931773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553145493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_67
      · exact prime_fiftySevenBC_1931773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1553145493) ^ 776572746 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1553145493) ^ 517715164 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1553145493) ^ 23181276 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1553145493) ^ 804 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1682075581 : Nat.Prime 1682075581 := by
  apply lucas_primality 1682075581 (2 : ZMod 1682075581)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (28034593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (28034593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682075581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_28034593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1682075581) ^ 841037790 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682075581) ^ 560691860 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682075581) ^ 336415116 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682075581) ^ 60 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1893081331 : Nat.Prime 1893081331 := by
  apply lucas_primality 1893081331 (2 : ZMod 1893081331)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (907, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (907, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1893081331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_907
      · exact prime_fiftySevenBC_3313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1893081331) ^ 946540665 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1893081331) ^ 631027110 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1893081331) ^ 378616266 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1893081331) ^ 270440190 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1893081331) ^ 2087190 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1893081331) ^ 571410 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2264821297 : Nat.Prime 2264821297 := by
  apply lucas_primality 2264821297 (5 : ZMod 2264821297)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79, 1), (597263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79, 1), (597263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2264821297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_597263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2264821297) ^ 1132410648 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2264821297) ^ 754940432 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2264821297) ^ 28668624 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2264821297) ^ 3792 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3185055631 : Nat.Prime 3185055631 := by
  apply lucas_primality 3185055631 (7 : ZMod 3185055631)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (1141597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (1141597, 1)] : List FactorBlock).map factorBlockValue).prod) = 3185055631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_31
      · exact prime_fiftySevenBC_1141597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3185055631) ^ 1592527815 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3185055631) ^ 1061685210 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3185055631) ^ 637011126 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3185055631) ^ 102743730 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3185055631) ^ 2790 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3221514551 : Nat.Prime 3221514551 := by
  apply lucas_primality 3221514551 (13 : ZMod 3221514551)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (2801317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (2801317, 1)] : List FactorBlock).map factorBlockValue).prod) = 3221514551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_2801317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3221514551) ^ 1610757275 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 3221514551) ^ 644302910 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 3221514551) ^ 140065850 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 3221514551) ^ 1150 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4062925457 : Nat.Prime 4062925457 := by
  apply lucas_primality 4062925457 (3 : ZMod 4062925457)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (253932841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (253932841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4062925457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_253932841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4062925457) ^ 2031462728 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4062925457) ^ 16 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4118533039 : Nat.Prime 4118533039 := by
  apply lucas_primality 4118533039 (3 : ZMod 4118533039)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (127, 1), (331, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (127, 1), (331, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) = 4118533039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_127
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_5443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4118533039) ^ 2059266519 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118533039) ^ 1372844346 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118533039) ^ 32429394 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118533039) ^ 12442698 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4118533039) ^ 756666 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4691472503 : Nat.Prime 4691472503 := by
  apply lucas_primality 4691472503 (5 : ZMod 4691472503)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (887, 1), (2644573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (887, 1), (2644573, 1)] : List FactorBlock).map factorBlockValue).prod) = 4691472503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_887
      · exact prime_fiftySevenBC_2644573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4691472503) ^ 2345736251 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4691472503) ^ 5289146 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4691472503) ^ 1774 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4709066389 : Nat.Prime 4709066389 := by
  apply lucas_primality 4709066389 (2 : ZMod 4709066389)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (30186323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (30186323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4709066389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_30186323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4709066389) ^ 2354533194 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4709066389) ^ 1569688796 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4709066389) ^ 362235876 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4709066389) ^ 156 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_6534328721 : Nat.Prime 6534328721 := by
  apply lucas_primality 6534328721 (6 : ZMod 6534328721)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (661, 1), (4261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (661, 1), (4261, 1)] : List FactorBlock).map factorBlockValue).prod) = 6534328721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_661
      · exact prime_fiftySevenBC_4261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6534328721) ^ 3267164360 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6534328721) ^ 1306865744 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6534328721) ^ 225321680 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6534328721) ^ 9885520 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6534328721) ^ 1533520 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_7091625707 : Nat.Prime 7091625707 := by
  apply lucas_primality 7091625707 (2 : ZMod 7091625707)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (307, 1), (13291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (307, 1), (13291, 1)] : List FactorBlock).map factorBlockValue).prod) = 7091625707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_307
      · exact prime_fiftySevenBC_13291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7091625707) ^ 3545812853 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7091625707) ^ 644693246 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7091625707) ^ 89767414 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7091625707) ^ 23099758 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7091625707) ^ 533566 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_7313931503 : Nat.Prime 7313931503 := by
  apply lucas_primality 7313931503 (5 : ZMod 7313931503)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1319, 1), (2772529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1319, 1), (2772529, 1)] : List FactorBlock).map factorBlockValue).prod) = 7313931503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1319
      · exact prime_fiftySevenBC_2772529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7313931503) ^ 3656965751 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 7313931503) ^ 5545058 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 7313931503) ^ 2638 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_7753900289 : Nat.Prime 7753900289 := by
  apply lucas_primality 7753900289 (3 : ZMod 7753900289)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (29, 1), (1044437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (29, 1), (1044437, 1)] : List FactorBlock).map factorBlockValue).prod) = 7753900289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_1044437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7753900289) ^ 3876950144 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7753900289) ^ 267375872 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7753900289) ^ 7424 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9039637757 : Nat.Prime 9039637757 := by
  apply lucas_primality 9039637757 (2 : ZMod 9039637757)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13669, 1), (165331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13669, 1), (165331, 1)] : List FactorBlock).map factorBlockValue).prod) = 9039637757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13669
      · exact prime_fiftySevenBC_165331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9039637757) ^ 4519818878 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9039637757) ^ 661324 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9039637757) ^ 54676 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9698448307 : Nat.Prime 9698448307 := by
  apply lucas_primality 9698448307 (5 : ZMod 9698448307)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23311, 1), (69341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23311, 1), (69341, 1)] : List FactorBlock).map factorBlockValue).prod) = 9698448307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_23311
      · exact prime_fiftySevenBC_69341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9698448307) ^ 4849224153 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9698448307) ^ 3232816102 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9698448307) ^ 416046 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9698448307) ^ 139866 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9726711493 : Nat.Prime 9726711493 := by
  apply lucas_primality 9726711493 (5 : ZMod 9726711493)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (467, 1), (1735673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (467, 1), (1735673, 1)] : List FactorBlock).map factorBlockValue).prod) = 9726711493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_467
      · exact prime_fiftySevenBC_1735673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9726711493) ^ 4863355746 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9726711493) ^ 3242237164 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9726711493) ^ 20828076 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 9726711493) ^ 5604 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_10106508133 : Nat.Prime 10106508133 := by
  apply lucas_primality 10106508133 (2 : ZMod 10106508133)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (59, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (59, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) = 10106508133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_59
      · exact prime_fiftySevenBC_32369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10106508133) ^ 5053254066 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10106508133) ^ 3368836044 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10106508133) ^ 1443786876 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10106508133) ^ 171296748 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10106508133) ^ 312228 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_12909687569 : Nat.Prime 12909687569 := by
  apply lucas_primality 12909687569 (3 : ZMod 12909687569)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (12042619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (12042619, 1)] : List FactorBlock).map factorBlockValue).prod) = 12909687569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_67
      · exact prime_fiftySevenBC_12042619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12909687569) ^ 6454843784 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12909687569) ^ 192681904 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12909687569) ^ 1072 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_13859729371 : Nat.Prime 13859729371 := by
  apply lucas_primality 13859729371 (3 : ZMod 13859729371)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (17110777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (17110777, 1)] : List FactorBlock).map factorBlockValue).prod) = 13859729371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17110777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13859729371) ^ 6929864685 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13859729371) ^ 4619909790 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13859729371) ^ 2771945874 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13859729371) ^ 810 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_15165060059 : Nat.Prime 15165060059 := by
  apply lucas_primality 15165060059 (2 : ZMod 15165060059)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40193, 1), (188653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40193, 1), (188653, 1)] : List FactorBlock).map factorBlockValue).prod) = 15165060059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_40193
      · exact prime_fiftySevenBC_188653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15165060059) ^ 7582530029 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15165060059) ^ 377306 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15165060059) ^ 80386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_15343491811 : Nat.Prime 15343491811 := by
  apply lucas_primality 15343491811 (13 : ZMod 15343491811)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12451, 1), (41077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12451, 1), (41077, 1)] : List FactorBlock).map factorBlockValue).prod) = 15343491811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_12451
      · exact prime_fiftySevenBC_41077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 15343491811) ^ 7671745905 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 15343491811) ^ 5114497270 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 15343491811) ^ 3068698362 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 15343491811) ^ 1232310 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 15343491811) ^ 373530 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_22603580213 : Nat.Prime 22603580213 := by
  apply lucas_primality 22603580213 (2 : ZMod 22603580213)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8999, 1), (627947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8999, 1), (627947, 1)] : List FactorBlock).map factorBlockValue).prod) = 22603580213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_8999
      · exact prime_fiftySevenBC_627947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22603580213) ^ 11301790106 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22603580213) ^ 2511788 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22603580213) ^ 35996 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_23179146521 : Nat.Prime 23179146521 := by
  apply lucas_primality 23179146521 (3 : ZMod 23179146521)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (30498877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (30498877, 1)] : List FactorBlock).map factorBlockValue).prod) = 23179146521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_30498877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23179146521) ^ 11589573260 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 23179146521) ^ 4635829304 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 23179146521) ^ 1219955080 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 23179146521) ^ 760 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_24525621983 : Nat.Prime 24525621983 := by
  apply lucas_primality 24525621983 (5 : ZMod 24525621983)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (17593703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (17593703, 1)] : List FactorBlock).map factorBlockValue).prod) = 24525621983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_41
      · exact prime_fiftySevenBC_17593703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24525621983) ^ 12262810991 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24525621983) ^ 1442683646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24525621983) ^ 598185902 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24525621983) ^ 1394 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_24850327889 : Nat.Prime 24850327889 := by
  apply lucas_primality 24850327889 (3 : ZMod 24850327889)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1553145493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1553145493, 1)] : List FactorBlock).map factorBlockValue).prod) = 24850327889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1553145493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 24850327889) ^ 12425163944 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24850327889) ^ 16 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_26298547777 : Nat.Prime 26298547777 := by
  apply lucas_primality 26298547777 (7 : ZMod 26298547777)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (15219067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (15219067, 1)] : List FactorBlock).map factorBlockValue).prod) = 26298547777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_15219067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 26298547777) ^ 13149273888 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 26298547777) ^ 8766182592 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 26298547777) ^ 1728 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_26443079501 : Nat.Prime 26443079501 := by
  apply lucas_primality 26443079501 (2 : ZMod 26443079501)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (239, 1), (221281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (239, 1), (221281, 1)] : List FactorBlock).map factorBlockValue).prod) = 26443079501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_239
      · exact prime_fiftySevenBC_221281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26443079501) ^ 13221539750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26443079501) ^ 5288615900 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26443079501) ^ 110640500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26443079501) ^ 119500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_27286007729 : Nat.Prime 27286007729 := by
  apply lucas_primality 27286007729 (3 : ZMod 27286007729)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (71, 1), (307, 1), (11177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (71, 1), (307, 1), (11177, 1)] : List FactorBlock).map factorBlockValue).prod) = 27286007729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_71
      · exact prime_fiftySevenBC_307
      · exact prime_fiftySevenBC_11177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27286007729) ^ 13643003864 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 27286007729) ^ 3898001104 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 27286007729) ^ 384309968 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 27286007729) ^ 88879504 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 27286007729) ^ 2441264 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_27488997001 : Nat.Prime 27488997001 := by
  apply lucas_primality 27488997001 (17 : ZMod 27488997001)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 3), (43, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 3), (43, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) = 27488997001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_43
      · exact prime_fiftySevenBC_23677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 27488997001) ^ 13744498500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 27488997001) ^ 9162999000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 27488997001) ^ 5497799400 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 27488997001) ^ 639279000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 27488997001) ^ 1161000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_28150851563 : Nat.Prime 28150851563 := by
  apply lucas_primality 28150851563 (2 : ZMod 28150851563)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (397, 1), (433, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (397, 1), (433, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) = 28150851563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_397
      · exact prime_fiftySevenBC_433
      · exact prime_fiftySevenBC_2213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28150851563) ^ 14075425781 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 28150851563) ^ 760833826 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 28150851563) ^ 70908946 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 28150851563) ^ 65013514 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 28150851563) ^ 12720674 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_29028075347 : Nat.Prime 29028075347 := by
  apply lucas_primality 29028075347 (2 : ZMod 29028075347)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51829, 1), (280037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51829, 1), (280037, 1)] : List FactorBlock).map factorBlockValue).prod) = 29028075347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_51829
      · exact prime_fiftySevenBC_280037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29028075347) ^ 14514037673 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 29028075347) ^ 560074 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 29028075347) ^ 103658 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_37525608139 : Nat.Prime 37525608139 := by
  apply lucas_primality 37525608139 (3 : ZMod 37525608139)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (269, 1), (701, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (269, 1), (701, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) = 37525608139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_269
      · exact prime_fiftySevenBC_701
      · exact prime_fiftySevenBC_1951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37525608139) ^ 18762804069 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 37525608139) ^ 12508536046 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 37525608139) ^ 2207388714 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 37525608139) ^ 139500402 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 37525608139) ^ 53531538 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 37525608139) ^ 19234038 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_57405551891 : Nat.Prime 57405551891 := by
  apply lucas_primality 57405551891 (2 : ZMod 57405551891)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (199, 1), (1696883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (199, 1), (1696883, 1)] : List FactorBlock).map factorBlockValue).prod) = 57405551891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_199
      · exact prime_fiftySevenBC_1696883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57405551891) ^ 28702775945 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 57405551891) ^ 11481110378 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 57405551891) ^ 3376797170 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 57405551891) ^ 288470110 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 57405551891) ^ 33830 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_58110321197 : Nat.Prime 58110321197 := by
  apply lucas_primality 58110321197 (2 : ZMod 58110321197)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (5821, 1), (146807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (5821, 1), (146807, 1)] : List FactorBlock).map factorBlockValue).prod) = 58110321197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_5821
      · exact prime_fiftySevenBC_146807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58110321197) ^ 29055160598 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58110321197) ^ 3418254188 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58110321197) ^ 9982876 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58110321197) ^ 395828 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_59101368149 : Nat.Prime 59101368149 := by
  apply lucas_primality 59101368149 (2 : ZMod 59101368149)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (643, 1), (792371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (643, 1), (792371, 1)] : List FactorBlock).map factorBlockValue).prod) = 59101368149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_643
      · exact prime_fiftySevenBC_792371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59101368149) ^ 29550684074 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59101368149) ^ 2037978212 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59101368149) ^ 91915036 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59101368149) ^ 74588 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_66326046337 : Nat.Prime 66326046337 := by
  apply lucas_primality 66326046337 (7 : ZMod 66326046337)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (19, 1), (83, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (19, 1), (83, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) = 66326046337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 66326046337) ^ 33163023168 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 66326046337) ^ 22108682112 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 66326046337) ^ 6029640576 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 66326046337) ^ 3490844544 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 66326046337) ^ 799108992 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 66326046337) ^ 19983744 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_77136918227 : Nat.Prime 77136918227 := by
  apply lucas_primality 77136918227 (2 : ZMod 77136918227)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1123, 1), (2020243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1123, 1), (2020243, 1)] : List FactorBlock).map factorBlockValue).prod) = 77136918227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_1123
      · exact prime_fiftySevenBC_2020243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77136918227) ^ 38568459113 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77136918227) ^ 4537465778 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77136918227) ^ 68688262 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77136918227) ^ 38182 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_85596819463 : Nat.Prime 85596819463 := by
  apply lucas_primality 85596819463 (3 : ZMod 85596819463)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (101, 1), (611467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (101, 1), (611467, 1)] : List FactorBlock).map factorBlockValue).prod) = 85596819463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_611467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85596819463) ^ 42798409731 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85596819463) ^ 28532273154 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85596819463) ^ 12228117066 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85596819463) ^ 7781529042 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85596819463) ^ 847493262 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85596819463) ^ 139986 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_89139753523 : Nat.Prime 89139753523 := by
  apply lucas_primality 89139753523 (2 : ZMod 89139753523)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (83, 1), (817331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (83, 1), (817331, 1)] : List FactorBlock).map factorBlockValue).prod) = 89139753523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_73
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_817331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89139753523) ^ 44569876761 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 89139753523) ^ 29713251174 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 89139753523) ^ 1221092514 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 89139753523) ^ 1073972934 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 89139753523) ^ 109062 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_92864789387 : Nat.Prime 92864789387 := by
  apply lucas_primality 92864789387 (2 : ZMod 92864789387)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (137, 1), (17838031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (137, 1), (17838031, 1)] : List FactorBlock).map factorBlockValue).prod) = 92864789387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_137
      · exact prime_fiftySevenBC_17838031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92864789387) ^ 46432394693 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92864789387) ^ 4887620494 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92864789387) ^ 677845178 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92864789387) ^ 5206 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_104721071341 : Nat.Prime 104721071341 := by
  apply lucas_primality 104721071341 (2 : ZMod 104721071341)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (102667717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (102667717, 1)] : List FactorBlock).map factorBlockValue).prod) = 104721071341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_102667717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104721071341) ^ 52360535670 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 104721071341) ^ 34907023780 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 104721071341) ^ 20944214268 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 104721071341) ^ 6160063020 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 104721071341) ^ 1020 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_114662002717 : Nat.Prime 114662002717 := by
  apply lucas_primality 114662002717 (5 : ZMod 114662002717)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3185055631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3185055631, 1)] : List FactorBlock).map factorBlockValue).prod) = 114662002717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_3185055631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 114662002717) ^ 57331001358 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 114662002717) ^ 38220667572 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 114662002717) ^ 36 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_117617916979 : Nat.Prime 117617916979 := by
  apply lucas_primality 117617916979 (2 : ZMod 117617916979)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6534328721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6534328721, 1)] : List FactorBlock).map factorBlockValue).prod) = 117617916979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_6534328721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 117617916979) ^ 58808958489 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 117617916979) ^ 39205972326 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 117617916979) ^ 18 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_119674037227 : Nat.Prime 119674037227 := by
  apply lucas_primality 119674037227 (2 : ZMod 119674037227)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (701, 1), (977, 1), (29123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (701, 1), (977, 1), (29123, 1)] : List FactorBlock).map factorBlockValue).prod) = 119674037227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_701
      · exact prime_fiftySevenBC_977
      · exact prime_fiftySevenBC_29123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119674037227) ^ 59837018613 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119674037227) ^ 39891345742 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119674037227) ^ 170719026 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119674037227) ^ 122491338 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119674037227) ^ 4109262 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_126867106273 : Nat.Prime 126867106273 := by
  apply lucas_primality 126867106273 (5 : ZMod 126867106273)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (337, 1), (1753, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (337, 1), (1753, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) = 126867106273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_337
      · exact prime_fiftySevenBC_1753
      · exact prime_fiftySevenBC_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 126867106273) ^ 63433553136 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 126867106273) ^ 42289035424 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 126867106273) ^ 376460256 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 126867106273) ^ 72371424 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 126867106273) ^ 56713056 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_130062009001 : Nat.Prime 130062009001 := by
  apply lucas_primality 130062009001 (13 : ZMod 130062009001)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (7, 1), (11, 1), (563039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (7, 1), (11, 1), (563039, 1)] : List FactorBlock).map factorBlockValue).prod) = 130062009001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_563039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 130062009001) ^ 65031004500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 130062009001) ^ 43354003000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 130062009001) ^ 26012401800 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 130062009001) ^ 18580287000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 130062009001) ^ 11823819000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 130062009001) ^ 231000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_156482247569 : Nat.Prime 156482247569 := by
  apply lucas_primality 156482247569 (3 : ZMod 156482247569)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (229, 1), (42708037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (229, 1), (42708037, 1)] : List FactorBlock).map factorBlockValue).prod) = 156482247569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_229
      · exact prime_fiftySevenBC_42708037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 156482247569) ^ 78241123784 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 156482247569) ^ 683328592 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 156482247569) ^ 3664 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_167545344221 : Nat.Prime 167545344221 := by
  apply lucas_primality 167545344221 (3 : ZMod 167545344221)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2851, 1), (2938361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2851, 1), (2938361, 1)] : List FactorBlock).map factorBlockValue).prod) = 167545344221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_2851
      · exact prime_fiftySevenBC_2938361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 167545344221) ^ 83772672110 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 167545344221) ^ 33509068844 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 167545344221) ^ 58767220 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 167545344221) ^ 57020 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_190932896527 : Nat.Prime 190932896527 := by
  apply lucas_primality 190932896527 (3 : ZMod 190932896527)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (308952907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (308952907, 1)] : List FactorBlock).map factorBlockValue).prod) = 190932896527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_103
      · exact prime_fiftySevenBC_308952907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190932896527) ^ 95466448263 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 190932896527) ^ 63644298842 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 190932896527) ^ 1853717442 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 190932896527) ^ 618 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_226978987523 : Nat.Prime 226978987523 := by
  apply lucas_primality 226978987523 (2 : ZMod 226978987523)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (229, 1), (70798187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (229, 1), (70798187, 1)] : List FactorBlock).map factorBlockValue).prod) = 226978987523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_229
      · exact prime_fiftySevenBC_70798187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226978987523) ^ 113489493761 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 226978987523) ^ 32425569646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 226978987523) ^ 991174618 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 226978987523) ^ 3206 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_252915429737 : Nat.Prime 252915429737 := by
  apply lucas_primality 252915429737 (3 : ZMod 252915429737)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (457, 1), (3007747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (457, 1), (3007747, 1)] : List FactorBlock).map factorBlockValue).prod) = 252915429737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_457
      · exact prime_fiftySevenBC_3007747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 252915429737) ^ 126457714868 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252915429737) ^ 10996323032 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252915429737) ^ 553425448 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 252915429737) ^ 84088 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_262635775817 : Nat.Prime 262635775817 := by
  apply lucas_primality 262635775817 (3 : ZMod 262635775817)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (325044277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (325044277, 1)] : List FactorBlock).map factorBlockValue).prod) = 262635775817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_325044277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 262635775817) ^ 131317887908 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 262635775817) ^ 2600354216 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 262635775817) ^ 808 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_263029322741 : Nat.Prime 263029322741 := by
  apply lucas_primality 263029322741 (3 : ZMod 263029322741)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4019, 1), (3272323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4019, 1), (3272323, 1)] : List FactorBlock).map factorBlockValue).prod) = 263029322741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_4019
      · exact prime_fiftySevenBC_3272323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 263029322741) ^ 131514661370 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 263029322741) ^ 52605864548 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 263029322741) ^ 65446460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 263029322741) ^ 80380 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_268495700791 : Nat.Prime 268495700791 := by
  apply lucas_primality 268495700791 (6 : ZMod 268495700791)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (109, 1), (82108777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (109, 1), (82108777, 1)] : List FactorBlock).map factorBlockValue).prod) = 268495700791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_109
      · exact prime_fiftySevenBC_82108777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 268495700791) ^ 134247850395 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 268495700791) ^ 89498566930 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 268495700791) ^ 53699140158 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 268495700791) ^ 2463263310 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 268495700791) ^ 3270 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_299303753789 : Nat.Prime 299303753789 := by
  apply lucas_primality 299303753789 (2 : ZMod 299303753789)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (71, 1), (331, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (71, 1), (331, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod) = 299303753789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_71
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_14407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 299303753789) ^ 149651876894 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 299303753789) ^ 23023365676 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 299303753789) ^ 17606103164 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 299303753789) ^ 4215545828 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 299303753789) ^ 904240948 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 299303753789) ^ 20774884 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_335591012221 : Nat.Prime 335591012221 := by
  apply lucas_primality 335591012221 (6 : ZMod 335591012221)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2791, 1), (2004007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2791, 1), (2004007, 1)] : List FactorBlock).map factorBlockValue).prod) = 335591012221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_2791
      · exact prime_fiftySevenBC_2004007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 335591012221) ^ 167795506110 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 335591012221) ^ 111863670740 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 335591012221) ^ 67118202444 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 335591012221) ^ 120240420 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 335591012221) ^ 167460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_360653646019 : Nat.Prime 360653646019 := by
  apply lucas_primality 360653646019 (2 : ZMod 360653646019)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (113, 1), (31290443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (113, 1), (31290443, 1)] : List FactorBlock).map factorBlockValue).prod) = 360653646019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_113
      · exact prime_fiftySevenBC_31290443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 360653646019) ^ 180326823009 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360653646019) ^ 120217882006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360653646019) ^ 21214920354 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360653646019) ^ 3191625186 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360653646019) ^ 11526 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_524670354913 : Nat.Prime 524670354913 := by
  apply lucas_primality 524670354913 (15 : ZMod 524670354913)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (151, 1), (3290377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (151, 1), (3290377, 1)] : List FactorBlock).map factorBlockValue).prod) = 524670354913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_151
      · exact prime_fiftySevenBC_3290377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 524670354913) ^ 262335177456 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 524670354913) ^ 174890118304 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 524670354913) ^ 47697304992 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 524670354913) ^ 3474638112 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (15 : ZMod 524670354913) ^ 159456 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_527923912507 : Nat.Prime 527923912507 := by
  apply lucas_primality 527923912507 (26 : ZMod 527923912507)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (988621559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (988621559, 1)] : List FactorBlock).map factorBlockValue).prod) = 527923912507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_89
      · exact prime_fiftySevenBC_988621559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 527923912507) ^ 263961956253 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (26 : ZMod 527923912507) ^ 175974637502 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (26 : ZMod 527923912507) ^ 5931729354 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (26 : ZMod 527923912507) ^ 534 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_540822946981 : Nat.Prime 540822946981 := by
  apply lucas_primality 540822946981 (2 : ZMod 540822946981)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1109, 1), (2311, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1109, 1), (2311, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 540822946981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_1109
      · exact prime_fiftySevenBC_2311
      · exact prime_fiftySevenBC_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 540822946981) ^ 270411473490 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 540822946981) ^ 180274315660 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 540822946981) ^ 108164589396 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 540822946981) ^ 487667220 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 540822946981) ^ 234021180 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 540822946981) ^ 153773940 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_568809563981 : Nat.Prime 568809563981 := by
  apply lucas_primality 568809563981 (10 : ZMod 568809563981)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (4062925457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (4062925457, 1)] : List FactorBlock).map factorBlockValue).prod) = 568809563981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_4062925457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 568809563981) ^ 284404781990 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 568809563981) ^ 113761912796 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 568809563981) ^ 81258509140 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 568809563981) ^ 140 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_638246313631 : Nat.Prime 638246313631 := by
  apply lucas_primality 638246313631 (11 : ZMod 638246313631)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7091625707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7091625707, 1)] : List FactorBlock).map factorBlockValue).prod) = 638246313631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7091625707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 638246313631) ^ 319123156815 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 638246313631) ^ 212748771210 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 638246313631) ^ 127649262726 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 638246313631) ^ 90 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_687877060501 : Nat.Prime 687877060501 := by
  apply lucas_primality 687877060501 (14 : ZMod 687877060501)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 3), (7, 1), (17, 1), (1284551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 3), (7, 1), (17, 1), (1284551, 1)] : List FactorBlock).map factorBlockValue).prod) = 687877060501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_1284551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 687877060501) ^ 343938530250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (14 : ZMod 687877060501) ^ 229292353500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (14 : ZMod 687877060501) ^ 137575412100 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (14 : ZMod 687877060501) ^ 98268151500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (14 : ZMod 687877060501) ^ 40463356500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (14 : ZMod 687877060501) ^ 535500 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_754932959273 : Nat.Prime 754932959273 := by
  apply lucas_primality 754932959273 (3 : ZMod 754932959273)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (22571, 1), (68539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (22571, 1), (68539, 1)] : List FactorBlock).map factorBlockValue).prod) = 754932959273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_22571
      · exact prime_fiftySevenBC_68539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 754932959273) ^ 377466479636 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754932959273) ^ 12375950152 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754932959273) ^ 33447032 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754932959273) ^ 11014648 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_791552718361 : Nat.Prime 791552718361 := by
  apply lucas_primality 791552718361 (7 : ZMod 791552718361)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (1217, 1), (1806703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (1217, 1), (1806703, 1)] : List FactorBlock).map factorBlockValue).prod) = 791552718361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_1217
      · exact prime_fiftySevenBC_1806703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 791552718361) ^ 395776359180 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 791552718361) ^ 263850906120 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 791552718361) ^ 158310543672 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 791552718361) ^ 650413080 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 791552718361) ^ 438120 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1038386902379 : Nat.Prime 1038386902379 := by
  apply lucas_primality 1038386902379 (2 : ZMod 1038386902379)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (643, 1), (10007, 1), (11527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (643, 1), (10007, 1), (11527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1038386902379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_643
      · exact prime_fiftySevenBC_10007
      · exact prime_fiftySevenBC_11527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1038386902379) ^ 519193451189 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038386902379) ^ 148340986054 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038386902379) ^ 1614909646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038386902379) ^ 103766054 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1038386902379) ^ 90083014 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1055777924009 : Nat.Prime 1055777924009 := by
  apply lucas_primality 1055777924009 (3 : ZMod 1055777924009)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (919, 1), (143604179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (919, 1), (143604179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1055777924009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_919
      · exact prime_fiftySevenBC_143604179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1055777924009) ^ 527888962004 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1055777924009) ^ 1148833432 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1055777924009) ^ 7352 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1240057991093 : Nat.Prime 1240057991093 := by
  apply lucas_primality 1240057991093 (2 : ZMod 1240057991093)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (101, 1), (383, 1), (96557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (101, 1), (383, 1), (96557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1240057991093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_383
      · exact prime_fiftySevenBC_96557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1240057991093) ^ 620028995546 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1240057991093) ^ 14940457724 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1240057991093) ^ 12277801892 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1240057991093) ^ 3237749324 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1240057991093) ^ 12842756 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1593845044993 : Nat.Prime 1593845044993 := by
  apply lucas_primality 1593845044993 (7 : ZMod 1593845044993)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (3371, 1), (205213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (3371, 1), (205213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1593845044993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_3371
      · exact prime_fiftySevenBC_205213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1593845044993) ^ 796922522496 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1593845044993) ^ 531281681664 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1593845044993) ^ 472810752 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1593845044993) ^ 7766784 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1947354286351 : Nat.Prime 1947354286351 := by
  apply lucas_primality 1947354286351 (3 : ZMod 1947354286351)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (389, 1), (3033971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (389, 1), (3033971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1947354286351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_389
      · exact prime_fiftySevenBC_3033971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1947354286351) ^ 973677143175 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1947354286351) ^ 649118095450 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1947354286351) ^ 389470857270 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1947354286351) ^ 177032207850 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1947354286351) ^ 5006052150 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1947354286351) ^ 641850 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2129767968001 : Nat.Prime 2129767968001 := by
  apply lucas_primality 2129767968001 (29 : ZMod 2129767968001)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 3), (613, 1), (36191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 3), (613, 1), (36191, 1)] : List FactorBlock).map factorBlockValue).prod) = 2129767968001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_613
      · exact prime_fiftySevenBC_36191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 2129767968001) ^ 1064883984000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (29 : ZMod 2129767968001) ^ 709922656000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (29 : ZMod 2129767968001) ^ 425953593600 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (29 : ZMod 2129767968001) ^ 3474336000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (29 : ZMod 2129767968001) ^ 58848000 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2475218571713 : Nat.Prime 2475218571713 := by
  apply lucas_primality 2475218571713 (3 : ZMod 2475218571713)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (70901, 1), (545483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (70901, 1), (545483, 1)] : List FactorBlock).map factorBlockValue).prod) = 2475218571713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_70901
      · exact prime_fiftySevenBC_545483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2475218571713) ^ 1237609285856 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2475218571713) ^ 34910912 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2475218571713) ^ 4537664 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2774037809383 : Nat.Prime 2774037809383 := by
  apply lucas_primality 2774037809383 (3 : ZMod 2774037809383)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (61, 1), (154680373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (61, 1), (154680373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2774037809383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_154680373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2774037809383) ^ 1387018904691 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774037809383) ^ 924679269794 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774037809383) ^ 396291115626 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774037809383) ^ 45476029662 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2774037809383) ^ 17934 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2857450501991 : Nat.Prime 2857450501991 := by
  apply lucas_primality 2857450501991 (21 : ZMod 2857450501991)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (34607, 1), (1179551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (34607, 1), (1179551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2857450501991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_34607
      · exact prime_fiftySevenBC_1179551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 2857450501991) ^ 1428725250995 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (21 : ZMod 2857450501991) ^ 571490100398 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (21 : ZMod 2857450501991) ^ 408207214570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (21 : ZMod 2857450501991) ^ 82568570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (21 : ZMod 2857450501991) ^ 2422490 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2932189997549 : Nat.Prime 2932189997549 := by
  apply lucas_primality 2932189997549 (2 : ZMod 2932189997549)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (104721071341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (104721071341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2932189997549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_104721071341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2932189997549) ^ 1466094998774 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2932189997549) ^ 418884285364 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2932189997549) ^ 28 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4453627877471 : Nat.Prime 4453627877471 := by
  apply lucas_primality 4453627877471 (11 : ZMod 4453627877471)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (131, 1), (463, 1), (7342799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (131, 1), (463, 1), (7342799, 1)] : List FactorBlock).map factorBlockValue).prod) = 4453627877471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_131
      · exact prime_fiftySevenBC_463
      · exact prime_fiftySevenBC_7342799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4453627877471) ^ 2226813938735 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4453627877471) ^ 890725575494 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4453627877471) ^ 33997159370 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4453627877471) ^ 9619066690 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4453627877471) ^ 606530 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_5807261613383 : Nat.Prime 5807261613383 := by
  apply lucas_primality 5807261613383 (5 : ZMod 5807261613383)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (7313931503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (7313931503, 1)] : List FactorBlock).map factorBlockValue).prod) = 5807261613383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_397
      · exact prime_fiftySevenBC_7313931503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5807261613383) ^ 2903630806691 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5807261613383) ^ 14627863006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5807261613383) ^ 794 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_6102966657511 : Nat.Prime 6102966657511 := by
  apply lucas_primality 6102966657511 (6 : ZMod 6102966657511)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (22603580213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (22603580213, 1)] : List FactorBlock).map factorBlockValue).prod) = 6102966657511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_22603580213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6102966657511) ^ 3051483328755 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6102966657511) ^ 2034322219170 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6102966657511) ^ 1220593331502 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 6102966657511) ^ 270 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_7046815021853 : Nat.Prime 7046815021853 := by
  apply lucas_primality 7046815021853 (2 : ZMod 7046815021853)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1283701, 1), (1372363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1283701, 1), (1372363, 1)] : List FactorBlock).map factorBlockValue).prod) = 7046815021853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1283701
      · exact prime_fiftySevenBC_1372363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7046815021853) ^ 3523407510926 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7046815021853) ^ 5489452 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7046815021853) ^ 5134804 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_7792391758303 : Nat.Prime 7792391758303 := by
  apply lucas_primality 7792391758303 (3 : ZMod 7792391758303)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (521, 1), (3617, 1), (229727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (521, 1), (3617, 1), (229727, 1)] : List FactorBlock).map factorBlockValue).prod) = 7792391758303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_521
      · exact prime_fiftySevenBC_3617
      · exact prime_fiftySevenBC_229727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7792391758303) ^ 3896195879151 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7792391758303) ^ 2597463919434 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7792391758303) ^ 14956606062 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7792391758303) ^ 2154379806 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7792391758303) ^ 33920226 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_10395366096301 : Nat.Prime 10395366096301 := by
  apply lucas_primality 10395366096301 (6 : ZMod 10395366096301)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (59, 1), (4099, 1), (143281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (59, 1), (4099, 1), (143281, 1)] : List FactorBlock).map factorBlockValue).prod) = 10395366096301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_59
      · exact prime_fiftySevenBC_4099
      · exact prime_fiftySevenBC_143281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10395366096301) ^ 5197683048150 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10395366096301) ^ 3465122032100 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10395366096301) ^ 2079073219260 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10395366096301) ^ 176192645700 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10395366096301) ^ 2536073700 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10395366096301) ^ 72552300 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_11207041479521 : Nat.Prime 11207041479521 := by
  apply lucas_primality 11207041479521 (6 : ZMod 11207041479521)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (37, 1), (1893081331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (37, 1), (1893081331, 1)] : List FactorBlock).map factorBlockValue).prod) = 11207041479521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_1893081331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11207041479521) ^ 5603520739760 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 11207041479521) ^ 2241408295904 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 11207041479521) ^ 302893012960 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 11207041479521) ^ 5920 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_11670809055547 : Nat.Prime 11670809055547 := by
  apply lucas_primality 11670809055547 (2 : ZMod 11670809055547)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (103, 1), (149, 1), (1753, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (103, 1), (149, 1), (1753, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) = 11670809055547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_103
      · exact prime_fiftySevenBC_149
      · exact prime_fiftySevenBC_1753
      · exact prime_fiftySevenBC_4253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11670809055547) ^ 5835404527773 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 3890269685182 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 686518179738 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 113308825782 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 78327577554 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 6657620682 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11670809055547) ^ 2744135682 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_11684125718107 : Nat.Prime 11684125718107 := by
  apply lucas_primality 11684125718107 (5 : ZMod 11684125718107)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1947354286351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1947354286351, 1)] : List FactorBlock).map factorBlockValue).prod) = 11684125718107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_1947354286351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11684125718107) ^ 5842062859053 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11684125718107) ^ 3894708572702 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11684125718107) ^ 6 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_12836706519569 : Nat.Prime 12836706519569 := by
  apply lucas_primality 12836706519569 (3 : ZMod 12836706519569)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (983, 1), (48009943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (983, 1), (48009943, 1)] : List FactorBlock).map factorBlockValue).prod) = 12836706519569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_983
      · exact prime_fiftySevenBC_48009943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12836706519569) ^ 6418353259784 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12836706519569) ^ 755100383504 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12836706519569) ^ 13058704496 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12836706519569) ^ 267376 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_14219308195319 : Nat.Prime 14219308195319 := by
  apply lucas_primality 14219308195319 (13 : ZMod 14219308195319)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (69109, 1), (1686491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (69109, 1), (1686491, 1)] : List FactorBlock).map factorBlockValue).prod) = 14219308195319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_69109
      · exact prime_fiftySevenBC_1686491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 14219308195319) ^ 7109654097659 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 14219308195319) ^ 233103413038 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 14219308195319) ^ 205751902 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (13 : ZMod 14219308195319) ^ 8431298 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_14538254667241 : Nat.Prime 14538254667241 := by
  apply lucas_primality 14538254667241 (11 : ZMod 14538254667241)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (797, 1), (2731, 1), (55661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (797, 1), (2731, 1), (55661, 1)] : List FactorBlock).map factorBlockValue).prod) = 14538254667241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_797
      · exact prime_fiftySevenBC_2731
      · exact prime_fiftySevenBC_55661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14538254667241) ^ 7269127333620 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 14538254667241) ^ 4846084889080 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 14538254667241) ^ 2907650933448 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 14538254667241) ^ 18241222920 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 14538254667241) ^ 5323418040 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 14538254667241) ^ 261192840 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_16422760812103 : Nat.Prime 16422760812103 := by
  apply lucas_primality 16422760812103 (3 : ZMod 16422760812103)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (353, 1), (7753900289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (353, 1), (7753900289, 1)] : List FactorBlock).map factorBlockValue).prod) = 16422760812103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_353
      · exact prime_fiftySevenBC_7753900289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16422760812103) ^ 8211380406051 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16422760812103) ^ 5474253604034 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16422760812103) ^ 46523401734 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16422760812103) ^ 2118 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_16638586949783 : Nat.Prime 16638586949783 := by
  apply lucas_primality 16638586949783 (5 : ZMod 16638586949783)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (121787, 1), (9758599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (121787, 1), (9758599, 1)] : List FactorBlock).map factorBlockValue).prod) = 16638586949783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_121787
      · exact prime_fiftySevenBC_9758599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16638586949783) ^ 8319293474891 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16638586949783) ^ 2376940992826 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16638586949783) ^ 136620386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16638586949783) ^ 1705018 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_19126140539917 : Nat.Prime 19126140539917 := by
  apply lucas_primality 19126140539917 (5 : ZMod 19126140539917)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1593845044993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1593845044993, 1)] : List FactorBlock).map factorBlockValue).prod) = 19126140539917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_1593845044993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19126140539917) ^ 9563070269958 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19126140539917) ^ 6375380179972 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 19126140539917) ^ 12 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_21951086332051 : Nat.Prime 21951086332051 := by
  apply lucas_primality 21951086332051 (2 : ZMod 21951086332051)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (29, 1), (1682075581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (29, 1), (1682075581, 1)] : List FactorBlock).map factorBlockValue).prod) = 21951086332051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_1682075581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21951086332051) ^ 10975543166025 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21951086332051) ^ 7317028777350 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21951086332051) ^ 4390217266410 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21951086332051) ^ 756934011450 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21951086332051) ^ 13050 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_25092205524073 : Nat.Prime 25092205524073 := by
  apply lucas_primality 25092205524073 (5 : ZMod 25092205524073)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (97, 1), (2459, 1), (162343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (97, 1), (2459, 1), (162343, 1)] : List FactorBlock).map factorBlockValue).prod) = 25092205524073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_2459
      · exact prime_fiftySevenBC_162343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25092205524073) ^ 12546102762036 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25092205524073) ^ 8364068508024 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25092205524073) ^ 258682531176 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25092205524073) ^ 10204231608 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 25092205524073) ^ 154562904 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_25673413039139 : Nat.Prime 25673413039139 := by
  apply lucas_primality 25673413039139 (2 : ZMod 25673413039139)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12836706519569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12836706519569, 1)] : List FactorBlock).map factorBlockValue).prod) = 25673413039139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_12836706519569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 25673413039139) ^ 12836706519569 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25673413039139) ^ 2 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_27464700324307 : Nat.Prime 27464700324307 := by
  apply lucas_primality 27464700324307 (2 : ZMod 27464700324307)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1951, 1), (335172443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1951, 1), (335172443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27464700324307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_1951
      · exact prime_fiftySevenBC_335172443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27464700324307) ^ 13732350162153 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27464700324307) ^ 9154900108102 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27464700324307) ^ 3923528617758 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27464700324307) ^ 14077242606 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27464700324307) ^ 81942 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_33167795470157 : Nat.Prime 33167795470157 := by
  apply lucas_primality 33167795470157 (2 : ZMod 33167795470157)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (277007, 1), (296377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (277007, 1), (296377, 1)] : List FactorBlock).map factorBlockValue).prod) = 33167795470157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_277007
      · exact prime_fiftySevenBC_296377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33167795470157) ^ 16583897735078 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167795470157) ^ 328394014556 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167795470157) ^ 119736308 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33167795470157) ^ 111910828 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_41160741354773 : Nat.Prime 41160741354773 := by
  apply lucas_primality 41160741354773 (2 : ZMod 41160741354773)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (791552718361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (791552718361, 1)] : List FactorBlock).map factorBlockValue).prod) = 41160741354773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_791552718361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41160741354773) ^ 20580370677386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41160741354773) ^ 3166210873444 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41160741354773) ^ 52 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_50753165169689 : Nat.Prime 50753165169689 := by
  apply lucas_primality 50753165169689 (3 : ZMod 50753165169689)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (74311, 1), (880133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (74311, 1), (880133, 1)] : List FactorBlock).map factorBlockValue).prod) = 50753165169689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_74311
      · exact prime_fiftySevenBC_880133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50753165169689) ^ 25376582584844 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 50753165169689) ^ 523228506904 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 50753165169689) ^ 682983208 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 50753165169689) ^ 57665336 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_51346826078279 : Nat.Prime 51346826078279 := by
  apply lucas_primality 51346826078279 (7 : ZMod 51346826078279)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25673413039139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25673413039139, 1)] : List FactorBlock).map factorBlockValue).prod) = 51346826078279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_25673413039139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 51346826078279) ^ 25673413039139 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 51346826078279) ^ 2 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_51434109035839 : Nat.Prime 51434109035839 := by
  apply lucas_primality 51434109035839 (3 : ZMod 51434109035839)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2857450501991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2857450501991, 1)] : List FactorBlock).map factorBlockValue).prod) = 51434109035839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_2857450501991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 51434109035839) ^ 25717054517919 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 51434109035839) ^ 17144703011946 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 51434109035839) ^ 18 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_141642139437641 : Nat.Prime 141642139437641 := by
  apply lucas_primality 141642139437641 (6 : ZMod 141642139437641)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (211859, 1), (16714199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (211859, 1), (16714199, 1)] : List FactorBlock).map factorBlockValue).prod) = 141642139437641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_211859
      · exact prime_fiftySevenBC_16714199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 141642139437641) ^ 70821069718820 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 141642139437641) ^ 28328427887528 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 141642139437641) ^ 668567960 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 141642139437641) ^ 8474360 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_167030930501753 : Nat.Prime 167030930501753 := by
  apply lucas_primality 167030930501753 (3 : ZMod 167030930501753)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (461171, 1), (45273589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (461171, 1), (45273589, 1)] : List FactorBlock).map factorBlockValue).prod) = 167030930501753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_461171
      · exact prime_fiftySevenBC_45273589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 167030930501753) ^ 83515465250876 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 167030930501753) ^ 362188712 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 167030930501753) ^ 3689368 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_172547235718097 : Nat.Prime 172547235718097 := by
  apply lucas_primality 172547235718097 (3 : ZMod 172547235718097)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (263029322741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (263029322741, 1)] : List FactorBlock).map factorBlockValue).prod) = 172547235718097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_41
      · exact prime_fiftySevenBC_263029322741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 172547235718097) ^ 86273617859048 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 172547235718097) ^ 4208469163856 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 172547235718097) ^ 656 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_181437885014921 : Nat.Prime 181437885014921 := by
  apply lucas_primality 181437885014921 (3 : ZMod 181437885014921)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (258551, 1), (17543723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (258551, 1), (17543723, 1)] : List FactorBlock).map factorBlockValue).prod) = 181437885014921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_258551
      · exact prime_fiftySevenBC_17543723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 181437885014921) ^ 90718942507460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 181437885014921) ^ 36287577002984 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 181437885014921) ^ 701748920 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 181437885014921) ^ 10342040 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_245905962296777 : Nat.Prime 245905962296777 := by
  apply lucas_primality 245905962296777 (3 : ZMod 245905962296777)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (331, 1), (92864789387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (331, 1), (92864789387, 1)] : List FactorBlock).map factorBlockValue).prod) = 245905962296777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_92864789387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 245905962296777) ^ 122952981148388 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 245905962296777) ^ 742918315096 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 245905962296777) ^ 2648 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_246964448128639 : Nat.Prime 246964448128639 := by
  apply lucas_primality 246964448128639 (3 : ZMod 246964448128639)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41160741354773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41160741354773, 1)] : List FactorBlock).map factorBlockValue).prod) = 246964448128639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_41160741354773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 246964448128639) ^ 123482224064319 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 246964448128639) ^ 82321482709546 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 246964448128639) ^ 6 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_252414956818967 : Nat.Prime 252414956818967 := by
  apply lucas_primality 252414956818967 (5 : ZMod 252414956818967)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (15731, 1), (422255347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (15731, 1), (422255347, 1)] : List FactorBlock).map factorBlockValue).prod) = 252414956818967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_15731
      · exact prime_fiftySevenBC_422255347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 252414956818967) ^ 126207478409483 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 252414956818967) ^ 13284997727314 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 252414956818967) ^ 16045703186 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 252414956818967) ^ 597778 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_261688584010339 : Nat.Prime 261688584010339 := by
  apply lucas_primality 261688584010339 (2 : ZMod 261688584010339)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (14538254667241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (14538254667241, 1)] : List FactorBlock).map factorBlockValue).prod) = 261688584010339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_14538254667241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 261688584010339) ^ 130844292005169 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261688584010339) ^ 87229528003446 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261688584010339) ^ 18 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_272870094884099 : Nat.Prime 272870094884099 := by
  apply lucas_primality 272870094884099 (2 : ZMod 272870094884099)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1049, 1), (130062009001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1049, 1), (130062009001, 1)] : List FactorBlock).map factorBlockValue).prod) = 272870094884099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1049
      · exact prime_fiftySevenBC_130062009001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 272870094884099) ^ 136435047442049 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 272870094884099) ^ 260124018002 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 272870094884099) ^ 2098 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_374233179466837 : Nat.Prime 374233179466837 := by
  apply lucas_primality 374233179466837 (2 : ZMod 374233179466837)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10395366096301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10395366096301, 1)] : List FactorBlock).map factorBlockValue).prod) = 374233179466837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_10395366096301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 374233179466837) ^ 187116589733418 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 374233179466837) ^ 124744393155612 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 374233179466837) ^ 36 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_424325934325309 : Nat.Prime 424325934325309 := by
  apply lucas_primality 424325934325309 (2 : ZMod 424325934325309)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 2), (211, 1), (16428319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 2), (211, 1), (16428319, 1)] : List FactorBlock).map factorBlockValue).prod) = 424325934325309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_101
      · exact prime_fiftySevenBC_211
      · exact prime_fiftySevenBC_16428319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 424325934325309) ^ 212162967162654 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424325934325309) ^ 141441978108436 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424325934325309) ^ 4201246874508 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424325934325309) ^ 2011023385428 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424325934325309) ^ 25828932 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_441705727692511 : Nat.Prime 441705727692511 := by
  apply lucas_primality 441705727692511 (6 : ZMod 441705727692511)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (149909, 1), (98216413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (149909, 1), (98216413, 1)] : List FactorBlock).map factorBlockValue).prod) = 441705727692511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_149909
      · exact prime_fiftySevenBC_98216413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 441705727692511) ^ 220852863846255 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 441705727692511) ^ 147235242564170 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 441705727692511) ^ 88341145538502 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 441705727692511) ^ 2946492390 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 441705727692511) ^ 4497270 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_817888800267491 : Nat.Prime 817888800267491 := by
  apply lucas_primality 817888800267491 (6 : ZMod 817888800267491)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11684125718107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11684125718107, 1)] : List FactorBlock).map factorBlockValue).prod) = 817888800267491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_11684125718107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 817888800267491) ^ 408944400133745 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 817888800267491) ^ 163577760053498 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 817888800267491) ^ 116841257181070 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 817888800267491) ^ 70 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_886267989176023 : Nat.Prime 886267989176023 := by
  apply lucas_primality 886267989176023 (5 : ZMod 886267989176023)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (1607, 1), (9533, 1), (38723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (1607, 1), (9533, 1), (38723, 1)] : List FactorBlock).map factorBlockValue).prod) = 886267989176023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_1607
      · exact prime_fiftySevenBC_9533
      · exact prime_fiftySevenBC_38723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 886267989176023) ^ 443133994588011 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 886267989176023) ^ 295422663058674 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 886267989176023) ^ 10677927580434 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 886267989176023) ^ 551504660346 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 886267989176023) ^ 92968424334 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 886267989176023) ^ 22887379314 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1126726484530721 : Nat.Prime 1126726484530721 := by
  apply lucas_primality 1126726484530721 (3 : ZMod 1126726484530721)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (89139753523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (89139753523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126726484530721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_89139753523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1126726484530721) ^ 563363242265360 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126726484530721) ^ 225345296906144 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126726484530721) ^ 14262360563680 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126726484530721) ^ 12640 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1292182458631453 : Nat.Prime 1292182458631453 := by
  apply lucas_primality 1292182458631453 (2 : ZMod 1292182458631453)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3701, 1), (9698448307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3701, 1), (9698448307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1292182458631453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_3701
      · exact prime_fiftySevenBC_9698448307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1292182458631453) ^ 646091229315726 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1292182458631453) ^ 430727486210484 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1292182458631453) ^ 349144139052 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1292182458631453) ^ 133236 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1380541516990147 : Nat.Prime 1380541516990147 := by
  apply lucas_primality 1380541516990147 (2 : ZMod 1380541516990147)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (73, 1), (1697, 1), (88445191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (73, 1), (1697, 1), (88445191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380541516990147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_73
      · exact prime_fiftySevenBC_1697
      · exact prime_fiftySevenBC_88445191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1380541516990147) ^ 690270758495073 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380541516990147) ^ 460180505663382 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380541516990147) ^ 197220216712878 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380541516990147) ^ 18911527630002 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380541516990147) ^ 813518866818 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1380541516990147) ^ 15609006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1512506147720767 : Nat.Prime 1512506147720767 := by
  apply lucas_primality 1512506147720767 (3 : ZMod 1512506147720767)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (67, 1), (20399, 1), (16767547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (67, 1), (20399, 1), (16767547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1512506147720767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_67
      · exact prime_fiftySevenBC_20399
      · exact prime_fiftySevenBC_16767547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1512506147720767) ^ 756253073860383 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1512506147720767) ^ 504168715906922 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1512506147720767) ^ 137500558883706 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1512506147720767) ^ 22574718622698 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1512506147720767) ^ 74146092834 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1512506147720767) ^ 90204378 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1670291510551507 : Nat.Prime 1670291510551507 := by
  apply lucas_primality 1670291510551507 (3 : ZMod 1670291510551507)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (593, 1), (156482247569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (593, 1), (156482247569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1670291510551507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_593
      · exact prime_fiftySevenBC_156482247569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1670291510551507) ^ 835145755275753 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1670291510551507) ^ 556763836850502 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1670291510551507) ^ 2816680456242 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1670291510551507) ^ 10674 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2166256823988833 : Nat.Prime 2166256823988833 := by
  apply lucas_primality 2166256823988833 (3 : ZMod 2166256823988833)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (677, 1), (47777, 1), (2092919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (677, 1), (47777, 1), (2092919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2166256823988833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_677
      · exact prime_fiftySevenBC_47777
      · exact prime_fiftySevenBC_2092919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2166256823988833) ^ 1083128411994416 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2166256823988833) ^ 3199788514016 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2166256823988833) ^ 45340997216 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2166256823988833) ^ 1035040928 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2242760377981007 : Nat.Prime 2242760377981007 := by
  apply lucas_primality 2242760377981007 (10 : ZMod 2242760377981007)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37, 1), (4001, 1), (582692263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37, 1), (4001, 1), (582692263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242760377981007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_4001
      · exact prime_fiftySevenBC_582692263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2242760377981007) ^ 1121380188990503 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242760377981007) ^ 172520029075462 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242760377981007) ^ 60615145350838 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242760377981007) ^ 560549957006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242760377981007) ^ 3848962 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2721228194211431 : Nat.Prime 2721228194211431 := by
  apply lucas_primality 2721228194211431 (7 : ZMod 2721228194211431)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (57787, 1), (4709066389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (57787, 1), (4709066389, 1)] : List FactorBlock).map factorBlockValue).prod) = 2721228194211431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_57787
      · exact prime_fiftySevenBC_4709066389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2721228194211431) ^ 1360614097105715 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2721228194211431) ^ 544245638842286 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2721228194211431) ^ 47090663890 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2721228194211431) ^ 577870 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2734100908328701 : Nat.Prime 2734100908328701 := by
  apply lucas_primality 2734100908328701 (10 : ZMod 2734100908328701)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (103, 1), (14081, 1), (2094601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (103, 1), (14081, 1), (2094601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2734100908328701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_103
      · exact prime_fiftySevenBC_14081
      · exact prime_fiftySevenBC_2094601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2734100908328701) ^ 1367050454164350 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2734100908328701) ^ 911366969442900 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2734100908328701) ^ 546820181665740 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2734100908328701) ^ 26544669012900 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2734100908328701) ^ 194169512700 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 2734100908328701) ^ 1305308700 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2927922712259267 : Nat.Prime 2927922712259267 := by
  apply lucas_primality 2927922712259267 (2 : ZMod 2927922712259267)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (751, 1), (20551, 1), (94854233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (751, 1), (20551, 1), (94854233, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927922712259267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_751
      · exact prime_fiftySevenBC_20551
      · exact prime_fiftySevenBC_94854233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2927922712259267) ^ 1463961356129633 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2927922712259267) ^ 3898698684766 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2927922712259267) ^ 142471057966 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2927922712259267) ^ 30867602 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4060960054173941 : Nat.Prime 4060960054173941 := by
  apply lucas_primality 4060960054173941 (2 : ZMod 4060960054173941)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (563, 1), (360653646019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (563, 1), (360653646019, 1)] : List FactorBlock).map factorBlockValue).prod) = 4060960054173941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_563
      · exact prime_fiftySevenBC_360653646019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4060960054173941) ^ 2030480027086970 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4060960054173941) ^ 812192010834788 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4060960054173941) ^ 7213072920380 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4060960054173941) ^ 11260 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4639673395012399 : Nat.Prime 4639673395012399 := by
  apply lucas_primality 4639673395012399 (6 : ZMod 4639673395012399)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1567, 1), (29028075347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1567, 1), (29028075347, 1)] : List FactorBlock).map factorBlockValue).prod) = 4639673395012399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_1567
      · exact prime_fiftySevenBC_29028075347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4639673395012399) ^ 2319836697506199 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4639673395012399) ^ 1546557798337466 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4639673395012399) ^ 272921964412494 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4639673395012399) ^ 2960863685394 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4639673395012399) ^ 159834 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_5804244548908843 : Nat.Prime 5804244548908843 := by
  apply lucas_primality 5804244548908843 (2 : ZMod 5804244548908843)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12541, 1), (77136918227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12541, 1), (77136918227, 1)] : List FactorBlock).map factorBlockValue).prod) = 5804244548908843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_12541
      · exact prime_fiftySevenBC_77136918227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5804244548908843) ^ 2902122274454421 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5804244548908843) ^ 1934748182969614 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5804244548908843) ^ 462821509362 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5804244548908843) ^ 75246 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_8121920108347883 : Nat.Prime 8121920108347883 := by
  apply lucas_primality 8121920108347883 (2 : ZMod 8121920108347883)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4060960054173941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4060960054173941, 1)] : List FactorBlock).map factorBlockValue).prod) = 8121920108347883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_4060960054173941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8121920108347883) ^ 4060960054173941 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8121920108347883) ^ 2 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9335170555156799 : Nat.Prime 9335170555156799 := by
  apply lucas_primality 9335170555156799 (11 : ZMod 9335170555156799)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (424325934325309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (424325934325309, 1)] : List FactorBlock).map factorBlockValue).prod) = 9335170555156799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_424325934325309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 9335170555156799) ^ 4667585277578399 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9335170555156799) ^ 848651868650618 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9335170555156799) ^ 22 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_10141877960468291 : Nat.Prime 10141877960468291 := by
  apply lucas_primality 10141877960468291 (2 : ZMod 10141877960468291)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1933, 1), (524670354913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1933, 1), (524670354913, 1)] : List FactorBlock).map factorBlockValue).prod) = 10141877960468291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_1933
      · exact prime_fiftySevenBC_524670354913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10141877960468291) ^ 5070938980234145 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10141877960468291) ^ 2028375592093658 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10141877960468291) ^ 5246703549130 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10141877960468291) ^ 19330 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_14796972392894591 : Nat.Prime 14796972392894591 := by
  apply lucas_primality 14796972392894591 (7 : ZMod 14796972392894591)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1394989, 1), (1060723231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1394989, 1), (1060723231, 1)] : List FactorBlock).map factorBlockValue).prod) = 14796972392894591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_1394989
      · exact prime_fiftySevenBC_1060723231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14796972392894591) ^ 7398486196447295 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14796972392894591) ^ 2959394478578918 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14796972392894591) ^ 10607232310 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14796972392894591) ^ 13949890 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_21413042834880569 : Nat.Prime 21413042834880569 := by
  apply lucas_primality 21413042834880569 (3 : ZMod 21413042834880569)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (601, 1), (4453627877471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (601, 1), (4453627877471, 1)] : List FactorBlock).map factorBlockValue).prod) = 21413042834880569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_601
      · exact prime_fiftySevenBC_4453627877471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21413042834880569) ^ 10706521417440284 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 21413042834880569) ^ 35629023019768 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 21413042834880569) ^ 4808 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_23572093084052647 : Nat.Prime 23572093084052647 := by
  apply lucas_primality 23572093084052647 (5 : ZMod 23572093084052647)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (107, 1), (191, 1), (827, 1), (1747723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (107, 1), (191, 1), (827, 1), (1747723, 1)] : List FactorBlock).map factorBlockValue).prod) = 23572093084052647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_107
      · exact prime_fiftySevenBC_191
      · exact prime_fiftySevenBC_827
      · exact prime_fiftySevenBC_1747723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23572093084052647) ^ 11786046542026323 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 7857364361350882 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 3367441869150378 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 1240636478108034 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 220299935364978 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 123414099916506 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 28503135530898 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 23572093084052647) ^ 13487316402 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_28763442926017871 : Nat.Prime 28763442926017871 := by
  apply lucas_primality 28763442926017871 (7 : ZMod 28763442926017871)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (7300459, 1), (56284999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (7300459, 1), (56284999, 1)] : List FactorBlock).map factorBlockValue).prod) = 28763442926017871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_7300459
      · exact prime_fiftySevenBC_56284999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28763442926017871) ^ 14381721463008935 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 28763442926017871) ^ 5752688585203574 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 28763442926017871) ^ 4109063275145410 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 28763442926017871) ^ 3939949930 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 28763442926017871) ^ 511032130 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_32073511398165577 : Nat.Prime 32073511398165577 := by
  apply lucas_primality 32073511398165577 (5 : ZMod 32073511398165577)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (65563, 1), (2264821297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (65563, 1), (2264821297, 1)] : List FactorBlock).map factorBlockValue).prod) = 32073511398165577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_65563
      · exact prime_fiftySevenBC_2264821297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32073511398165577) ^ 16036755699082788 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32073511398165577) ^ 10691170466055192 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32073511398165577) ^ 489201400152 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32073511398165577) ^ 14161608 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_33747446612775307 : Nat.Prime 33747446612775307 := by
  apply lucas_primality 33747446612775307 (5 : ZMod 33747446612775307)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (181437885014921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (181437885014921, 1)] : List FactorBlock).map factorBlockValue).prod) = 33747446612775307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_31
      · exact prime_fiftySevenBC_181437885014921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33747446612775307) ^ 16873723306387653 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 33747446612775307) ^ 11249148870925102 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 33747446612775307) ^ 1088627310089526 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 33747446612775307) ^ 186 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_56940716243176861 : Nat.Prime 56940716243176861 := by
  apply lucas_primality 56940716243176861 (6 : ZMod 56940716243176861)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11087, 1), (85596819463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11087, 1), (85596819463, 1)] : List FactorBlock).map factorBlockValue).prod) = 56940716243176861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_11087
      · exact prime_fiftySevenBC_85596819463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 56940716243176861) ^ 28470358121588430 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 56940716243176861) ^ 18980238747725620 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 56940716243176861) ^ 11388143248635372 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 56940716243176861) ^ 5135809167780 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 56940716243176861) ^ 665220 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_60851267762809747 : Nat.Prime 60851267762809747 := by
  apply lucas_primality 60851267762809747 (2 : ZMod 60851267762809747)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10141877960468291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10141877960468291, 1)] : List FactorBlock).map factorBlockValue).prod) = 60851267762809747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_10141877960468291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60851267762809747) ^ 30425633881404873 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60851267762809747) ^ 20283755920936582 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60851267762809747) ^ 6 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_70578410262193441 : Nat.Prime 70578410262193441 := by
  apply lucas_primality 70578410262193441 (7 : ZMod 70578410262193441)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (673, 1), (223481, 1), (325877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (673, 1), (223481, 1), (325877, 1)] : List FactorBlock).map factorBlockValue).prod) = 70578410262193441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_673
      · exact prime_fiftySevenBC_223481
      · exact prime_fiftySevenBC_325877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 70578410262193441) ^ 35289205131096720 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 70578410262193441) ^ 23526136754064480 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 70578410262193441) ^ 14115682052438688 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 70578410262193441) ^ 104871337685280 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 70578410262193441) ^ 315813918240 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 70578410262193441) ^ 216579906720 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_86078565620013899 : Nat.Prime 86078565620013899 := by
  apply lucas_primality 86078565620013899 (2 : ZMod 86078565620013899)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (167, 1), (1261487, 1), (2106173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (167, 1), (1261487, 1), (2106173, 1)] : List FactorBlock).map factorBlockValue).prod) = 86078565620013899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_167
      · exact prime_fiftySevenBC_1261487
      · exact prime_fiftySevenBC_2106173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 86078565620013899) ^ 43039282810006949 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86078565620013899) ^ 887407892989834 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86078565620013899) ^ 515440512694694 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86078565620013899) ^ 68235792854 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86078565620013899) ^ 40869655826 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_111208654882691537 : Nat.Prime 111208654882691537 := by
  apply lucas_primality 111208654882691537 (3 : ZMod 111208654882691537)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (277, 1), (25092205524073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (277, 1), (25092205524073, 1)] : List FactorBlock).map factorBlockValue).prod) = 111208654882691537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_277
      · exact prime_fiftySevenBC_25092205524073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 111208654882691537) ^ 55604327441345768 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 111208654882691537) ^ 401475288385168 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 111208654882691537) ^ 4432 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_146155149873652477 : Nat.Prime 146155149873652477 := by
  apply lucas_primality 146155149873652477 (2 : ZMod 146155149873652477)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (163, 1), (272759, 1), (14418251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (163, 1), (272759, 1), (14418251, 1)] : List FactorBlock).map factorBlockValue).prod) = 146155149873652477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_163
      · exact prime_fiftySevenBC_272759
      · exact prime_fiftySevenBC_14418251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146155149873652477) ^ 73077574936826238 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146155149873652477) ^ 48718383291217492 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146155149873652477) ^ 7692376309139604 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146155149873652477) ^ 896657361188052 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146155149873652477) ^ 535839880164 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146155149873652477) ^ 10136815476 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_151280562751723667 : Nat.Prime 151280562751723667 := by
  apply lucas_primality 151280562751723667 (2 : ZMod 151280562751723667)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (2221031, 1), (318283949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (2221031, 1), (318283949, 1)] : List FactorBlock).map factorBlockValue).prod) = 151280562751723667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_107
      · exact prime_fiftySevenBC_2221031
      · exact prime_fiftySevenBC_318283949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151280562751723667) ^ 75640281375861833 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 151280562751723667) ^ 1413837035062838 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 151280562751723667) ^ 68112765086 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 151280562751723667) ^ 475300634 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_573511814021432159 : Nat.Prime 573511814021432159 := by
  apply lucas_primality 573511814021432159 (17 : ZMod 573511814021432159)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (1213, 1), (2269, 1), (7039, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (1213, 1), (2269, 1), (7039, 1), (26863, 1)] : List FactorBlock).map factorBlockValue).prod) = 573511814021432159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_1213
      · exact prime_fiftySevenBC_2269
      · exact prime_fiftySevenBC_7039
      · exact prime_fiftySevenBC_26863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 573511814021432159) ^ 286755907010716079 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 30184832316917482 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 19776269449014902 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 472804463331766 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 252759724116982 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 81476319650722 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 573511814021432159) ^ 21349507278466 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_846940923146321293 : Nat.Prime 846940923146321293 := by
  apply lucas_primality 846940923146321293 (2 : ZMod 846940923146321293)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (70578410262193441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (70578410262193441, 1)] : List FactorBlock).map factorBlockValue).prod) = 846940923146321293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_70578410262193441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 846940923146321293) ^ 423470461573160646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 846940923146321293) ^ 282313641048773764 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 846940923146321293) ^ 12 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_850747474409188379 : Nat.Prime 850747474409188379 := by
  apply lucas_primality 850747474409188379 (2 : ZMod 850747474409188379)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (919, 1), (2475218571713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (919, 1), (2475218571713, 1)] : List FactorBlock).map factorBlockValue).prod) = 850747474409188379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_919
      · exact prime_fiftySevenBC_2475218571713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 850747474409188379) ^ 425373737204594189 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 850747474409188379) ^ 77340679491744398 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 850747474409188379) ^ 50043969082893434 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 850747474409188379) ^ 925731745820662 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 850747474409188379) ^ 343706 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1234867575043573529 : Nat.Prime 1234867575043573529 := by
  apply lucas_primality 1234867575043573529 (3 : ZMod 1234867575043573529)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (3527, 1), (268495700791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (3527, 1), (268495700791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1234867575043573529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_163
      · exact prime_fiftySevenBC_3527
      · exact prime_fiftySevenBC_268495700791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1234867575043573529) ^ 617433787521786764 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1234867575043573529) ^ 7575874693518856 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1234867575043573529) ^ 350118393831464 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1234867575043573529) ^ 4599208 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1274231550665504117 : Nat.Prime 1274231550665504117 := by
  apply lucas_primality 1274231550665504117 (2 : ZMod 1274231550665504117)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (2417, 1), (3347, 1), (296076787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (2417, 1), (3347, 1), (296076787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1274231550665504117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_2417
      · exact prime_fiftySevenBC_3347
      · exact prime_fiftySevenBC_296076787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1274231550665504117) ^ 637115775332752058 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1274231550665504117) ^ 182033078666500588 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1274231550665504117) ^ 67064818456079164 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1274231550665504117) ^ 527195511239348 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1274231550665504117) ^ 380708560103228 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1274231550665504117) ^ 4303719868 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1556614551212765953 : Nat.Prime 1556614551212765953 := by
  apply lucas_primality 1556614551212765953 (7 : ZMod 1556614551212765953)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (23, 1), (79, 1), (12097, 1), (5424233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (23, 1), (79, 1), (12097, 1), (5424233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1556614551212765953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_12097
      · exact prime_fiftySevenBC_5424233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1556614551212765953) ^ 778307275606382976 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 518871517070921984 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 91565561836045056 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 67678893530989824 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 19703981660921088 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 128677734249216 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1556614551212765953) ^ 286974130944 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1715987573908275307 : Nat.Prime 1715987573908275307 := by
  apply lucas_primality 1715987573908275307 (2 : ZMod 1715987573908275307)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10159477, 1), (28150851563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10159477, 1), (28150851563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1715987573908275307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_10159477
      · exact prime_fiftySevenBC_28150851563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1715987573908275307) ^ 857993786954137653 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1715987573908275307) ^ 571995857969425102 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1715987573908275307) ^ 168905109378 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1715987573908275307) ^ 60956862 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2134698004544397389 : Nat.Prime 2134698004544397389 := by
  apply lucas_primality 2134698004544397389 (2 : ZMod 2134698004544397389)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (22741, 1), (307589, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (22741, 1), (307589, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod) = 2134698004544397389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_149
      · exact prime_fiftySevenBC_22741
      · exact prime_fiftySevenBC_307589
      · exact prime_fiftySevenBC_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2134698004544397389) ^ 1067349002272198694 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134698004544397389) ^ 14326832245264412 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134698004544397389) ^ 93870014711068 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134698004544397389) ^ 6940098652892 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134698004544397389) ^ 4168949343604 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3651076065768584821 : Nat.Prime 3651076065768584821 := by
  apply lucas_primality 3651076065768584821 (2 : ZMod 3651076065768584821)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (60851267762809747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (60851267762809747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3651076065768584821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_60851267762809747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3651076065768584821) ^ 1825538032884292410 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3651076065768584821) ^ 1217025355256194940 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3651076065768584821) ^ 730215213153716964 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3651076065768584821) ^ 60 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4003045154941350737 : Nat.Prime 4003045154941350737 := by
  apply lucas_primality 4003045154941350737 (3 : ZMod 4003045154941350737)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (97, 1), (331, 1), (7792391758303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (97, 1), (331, 1), (7792391758303, 1)] : List FactorBlock).map factorBlockValue).prod) = 4003045154941350737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_97
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_7792391758303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4003045154941350737) ^ 2001522577470675368 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4003045154941350737) ^ 41268506751972688 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4003045154941350737) ^ 12093792008886256 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4003045154941350737) ^ 513712 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4029173908681858297 : Nat.Prime 4029173908681858297 := by
  apply lucas_primality 4029173908681858297 (10 : ZMod 4029173908681858297)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (149, 1), (1126726484530721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (149, 1), (1126726484530721, 1)] : List FactorBlock).map factorBlockValue).prod) = 4029173908681858297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_149
      · exact prime_fiftySevenBC_1126726484530721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4029173908681858297) ^ 2014586954340929148 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 4029173908681858297) ^ 1343057969560619432 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 4029173908681858297) ^ 27041435628737304 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 4029173908681858297) ^ 3576 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_12228292723748157977 : Nat.Prime 12228292723748157977 := by
  apply lucas_primality 12228292723748157977 (3 : ZMod 12228292723748157977)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (371136173, 1), (4118533039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (371136173, 1), (4118533039, 1)] : List FactorBlock).map factorBlockValue).prod) = 12228292723748157977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_371136173
      · exact prime_fiftySevenBC_4118533039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12228292723748157977) ^ 6114146361874078988 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12228292723748157977) ^ 32948264312 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12228292723748157977) ^ 2969089384 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_17523805131372495379 : Nat.Prime 17523805131372495379 := by
  apply lucas_primality 17523805131372495379 (2 : ZMod 17523805131372495379)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (263, 1), (839, 1), (167545344221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (263, 1), (839, 1), (167545344221, 1)] : List FactorBlock).map factorBlockValue).prod) = 17523805131372495379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_263
      · exact prime_fiftySevenBC_839
      · exact prime_fiftySevenBC_167545344221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17523805131372495379) ^ 8761902565686247689 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17523805131372495379) ^ 5841268377124165126 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17523805131372495379) ^ 221820318118639182 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17523805131372495379) ^ 66630437761872606 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17523805131372495379) ^ 20886537701278302 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17523805131372495379) ^ 104591418 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_18031521274714769693 : Nat.Prime 18031521274714769693 := by
  apply lucas_primality 18031521274714769693 (5 : ZMod 18031521274714769693)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (19, 2), (83, 1), (1811, 1), (375903491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (19, 2), (83, 1), (1811, 1), (375903491, 1)] : List FactorBlock).map factorBlockValue).prod) = 18031521274714769693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_1811
      · exact prime_fiftySevenBC_375903491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18031521274714769693) ^ 9015760637357384846 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 1387040098054982284 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 1060677722042045276 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 949027435511303668 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 217247244273671924 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 9956665529936372 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 18031521274714769693) ^ 47968485812 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_20076883162360473959 : Nat.Prime 20076883162360473959 := by
  apply lucas_primality 20076883162360473959 (11 : ZMod 20076883162360473959)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (28763442926017871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (28763442926017871, 1)] : List FactorBlock).map factorBlockValue).prod) = 20076883162360473959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_349
      · exact prime_fiftySevenBC_28763442926017871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 20076883162360473959) ^ 10038441581180236979 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 20076883162360473959) ^ 57526885852035742 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 20076883162360473959) ^ 698 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_20286154326672070381 : Nat.Prime 20286154326672070381 := by
  apply lucas_primality 20286154326672070381 (2 : ZMod 20286154326672070381)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (33637, 1), (832159, 1), (4026277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (33637, 1), (832159, 1), (4026277, 1)] : List FactorBlock).map factorBlockValue).prod) = 20286154326672070381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_33637
      · exact prime_fiftySevenBC_832159
      · exact prime_fiftySevenBC_4026277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20286154326672070381) ^ 10143077163336035190 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20286154326672070381) ^ 6762051442224023460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20286154326672070381) ^ 4057230865334414076 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20286154326672070381) ^ 603090475567740 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20286154326672070381) ^ 24377738300820 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20286154326672070381) ^ 5038439810940 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_34848684271648693373 : Nat.Prime 34848684271648693373 := by
  apply lucas_primality 34848684271648693373 (2 : ZMod 34848684271648693373)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (79, 1), (5804244548908843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (79, 1), (5804244548908843, 1)] : List FactorBlock).map factorBlockValue).prod) = 34848684271648693373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_79
      · exact prime_fiftySevenBC_5804244548908843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34848684271648693373) ^ 17424342135824346686 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34848684271648693373) ^ 1834141277455194388 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34848684271648693373) ^ 441122585717072068 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34848684271648693373) ^ 6004 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_232666360355967705187 : Nat.Prime 232666360355967705187 := by
  apply lucas_primality 232666360355967705187 (2 : ZMod 232666360355967705187)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (656122319, 1), (59101368149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (656122319, 1), (59101368149, 1)] : List FactorBlock).map factorBlockValue).prod) = 232666360355967705187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_656122319
      · exact prime_fiftySevenBC_59101368149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 232666360355967705187) ^ 116333180177983852593 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 232666360355967705187) ^ 77555453451989235062 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 232666360355967705187) ^ 354608208894 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 232666360355967705187) ^ 3936733914 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_240971020340726598187 : Nat.Prime 240971020340726598187 := by
  apply lucas_primality 240971020340726598187 (2 : ZMod 240971020340726598187)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (3651076065768584821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (3651076065768584821, 1)] : List FactorBlock).map factorBlockValue).prod) = 240971020340726598187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_3651076065768584821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240971020340726598187) ^ 120485510170363299093 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 240971020340726598187) ^ 80323673446908866062 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 240971020340726598187) ^ 21906456394611508926 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 240971020340726598187) ^ 66 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_387903613671833700169 : Nat.Prime 387903613671833700169 := by
  apply lucas_primality 387903613671833700169 (17 : ZMod 387903613671833700169)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (13, 1), (61, 1), (331, 1), (2932189997549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (13, 1), (61, 1), (331, 1), (2932189997549, 1)] : List FactorBlock).map factorBlockValue).prod) = 387903613671833700169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_2932189997549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 387903613671833700169) ^ 193951806835916850084 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 129301204557277900056 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 55414801953119100024 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 29838739513217976936 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 6359075633964486888 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 1171914240700403928 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 387903613671833700169) ^ 132291432 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_570485891228536547821 : Nat.Prime 570485891228536547821 := by
  apply lucas_primality 570485891228536547821 (2 : ZMod 570485891228536547821)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (17, 1), (29, 1), (53, 1), (2039, 1), (58363, 1), (339761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (17, 1), (29, 1), (53, 1), (2039, 1), (58363, 1), (339761, 1)] : List FactorBlock).map factorBlockValue).prod) = 570485891228536547821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_2039
      · exact prime_fiftySevenBC_58363
      · exact prime_fiftySevenBC_339761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 570485891228536547821) ^ 285242945614268273910 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 190161963742845515940 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 114097178245707309564 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 33557993601678620460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 19671927283742639580 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 10763884740161066940 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 279787097218507380 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 9774786957979140 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 570485891228536547821) ^ 1679079974536620 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_707390925388477988681 : Nat.Prime 707390925388477988681 := by
  apply lucas_primality 707390925388477988681 (3 : ZMod 707390925388477988681)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (146155149873652477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (146155149873652477, 1)] : List FactorBlock).map factorBlockValue).prod) = 707390925388477988681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_146155149873652477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 707390925388477988681) ^ 353695462694238994340 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 707390925388477988681) ^ 141478185077695597736 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 707390925388477988681) ^ 64308265944407089880 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 707390925388477988681) ^ 4840 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3746212739443598890507 : Nat.Prime 3746212739443598890507 := by
  apply lucas_primality 3746212739443598890507 (3 : ZMod 3746212739443598890507)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (278393, 1), (2242760377981007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (278393, 1), (2242760377981007, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746212739443598890507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_278393
      · exact prime_fiftySevenBC_2242760377981007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3746212739443598890507) ^ 1873106369721799445253 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3746212739443598890507) ^ 1248737579814532963502 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3746212739443598890507) ^ 13456562267886042 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3746212739443598890507) ^ 1670358 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_5176611581508339646237 : Nat.Prime 5176611581508339646237 := by
  apply lucas_primality 5176611581508339646237 (2 : ZMod 5176611581508339646237)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1021, 1), (2203, 1), (8923, 1), (20107, 1), (46477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1021, 1), (2203, 1), (8923, 1), (20107, 1), (46477, 1)] : List FactorBlock).map factorBlockValue).prod) = 5176611581508339646237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_1021
      · exact prime_fiftySevenBC_2203
      · exact prime_fiftySevenBC_8923
      · exact prime_fiftySevenBC_20107
      · exact prime_fiftySevenBC_46477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5176611581508339646237) ^ 2588305790754169823118 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 1725537193836113215412 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 225070068761232158532 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 5070138669449891916 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 2349800990244366612 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 580142506052710932 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 257453204431707348 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5176611581508339646237) ^ 111380071465635468 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_24314682499668368839949 : Nat.Prime 24314682499668368839949 := by
  apply lucas_primality 24314682499668368839949 (3 : ZMod 24314682499668368839949)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (71633, 1), (3763027, 1), (3221514551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (71633, 1), (3763027, 1), (3221514551, 1)] : List FactorBlock).map factorBlockValue).prod) = 24314682499668368839949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_71633
      · exact prime_fiftySevenBC_3763027
      · exact prime_fiftySevenBC_3221514551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24314682499668368839949) ^ 12157341249834184419974 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24314682499668368839949) ^ 3473526071381195548564 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24314682499668368839949) ^ 339434094616564556 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24314682499668368839949) ^ 6461469051289924 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24314682499668368839949) ^ 7547593566548 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_39868880430333875247311 : Nat.Prime 39868880430333875247311 := by
  apply lucas_primality 39868880430333875247311 (23 : ZMod 39868880430333875247311)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (2251, 1), (7529, 1), (89083, 1), (31816201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (2251, 1), (7529, 1), (89083, 1), (31816201, 1)] : List FactorBlock).map factorBlockValue).prod) = 39868880430333875247311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_83
      · exact prime_fiftySevenBC_2251
      · exact prime_fiftySevenBC_7529
      · exact prime_fiftySevenBC_89083
      · exact prime_fiftySevenBC_31816201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 39868880430333875247311) ^ 19934440215166937623655 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 7973776086066775049462 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 480347956991974400570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 17711630577669424810 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 5295375272988959390 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 447547572829090570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (23 : ZMod 39868880430333875247311) ^ 1253099967225310 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_46100663568530555573291 : Nat.Prime 46100663568530555573291 := by
  apply lucas_primality 46100663568530555573291 (6 : ZMod 46100663568530555573291)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (29, 1), (12228292723748157977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (29, 1), (12228292723748157977, 1)] : List FactorBlock).map factorBlockValue).prod) = 46100663568530555573291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_12228292723748157977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 46100663568530555573291) ^ 23050331784265277786645 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 46100663568530555573291) ^ 9220132713706111114658 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 46100663568530555573291) ^ 3546204889886965813330 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 46100663568530555573291) ^ 1589678054087260537010 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (6 : ZMod 46100663568530555573291) ^ 3770 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_98732407572055236949043 : Nat.Prime 98732407572055236949043 := by
  apply lucas_primality 98732407572055236949043 (2 : ZMod 98732407572055236949043)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23179146521, 1), (2129767968001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23179146521, 1), (2129767968001, 1)] : List FactorBlock).map factorBlockValue).prod) = 98732407572055236949043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23179146521
      · exact prime_fiftySevenBC_2129767968001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98732407572055236949043) ^ 49366203786027618474521 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98732407572055236949043) ^ 4259535936002 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98732407572055236949043) ^ 46358293042 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_179214712835212737579011 : Nat.Prime 179214712835212737579011 := by
  apply lucas_primality 179214712835212737579011 (2 : ZMod 179214712835212737579011)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (37, 1), (331, 1), (86078565620013899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (37, 1), (331, 1), (86078565620013899, 1)] : List FactorBlock).map factorBlockValue).prod) = 179214712835212737579011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_17
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_86078565620013899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 179214712835212737579011) ^ 89607356417606368789505 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179214712835212737579011) ^ 35842942567042547515802 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179214712835212737579011) ^ 10542041931483102210530 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179214712835212737579011) ^ 4843640887438182096730 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179214712835212737579011) ^ 541434177749887424710 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179214712835212737579011) ^ 2081990 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_211273967739072094355347 : Nat.Prime 211273967739072094355347 := by
  apply lucas_primality 211273967739072094355347 (3 : ZMod 211273967739072094355347)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (143194283, 1), (245905962296777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (143194283, 1), (245905962296777, 1)] : List FactorBlock).map factorBlockValue).prod) = 211273967739072094355347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_143194283
      · exact prime_fiftySevenBC_245905962296777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 211273967739072094355347) ^ 105636983869536047177673 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 211273967739072094355347) ^ 70424655913024031451782 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 211273967739072094355347) ^ 1475435773780662 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 211273967739072094355347) ^ 859165698 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_478844424504990795677969 : Nat.Prime 478844424504990795677969 := by
  apply lucas_primality 478844424504990795677969 (3 : ZMod 478844424504990795677969)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113, 1), (181, 1), (271, 1), (5501, 1), (49633, 1), (19775887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113, 1), (181, 1), (271, 1), (5501, 1), (49633, 1), (19775887, 1)] : List FactorBlock).map factorBlockValue).prod) = 478844424504990795677969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_113
      · exact prime_fiftySevenBC_181
      · exact prime_fiftySevenBC_271
      · exact prime_fiftySevenBC_5501
      · exact prime_fiftySevenBC_49633
      · exact prime_fiftySevenBC_19775887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 478844424504990795677969) ^ 239422212252495397838984 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 4237561278805228280336 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 2645549306657407710928 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 1766953595959375629808 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 87046795947098853968 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 9647702627384820496 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 478844424504990795677969) ^ 24213549789447664 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1286790383690297300900279 : Nat.Prime 1286790383690297300900279 := by
  apply lucas_primality 1286790383690297300900279 (17 : ZMod 1286790383690297300900279)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1693, 1), (428801, 1), (886267989176023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1693, 1), (428801, 1), (886267989176023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1286790383690297300900279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1693
      · exact prime_fiftySevenBC_428801
      · exact prime_fiftySevenBC_886267989176023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1286790383690297300900279) ^ 643395191845148650450139 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 1286790383690297300900279) ^ 760065200053335676846 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 1286790383690297300900279) ^ 3000903411350013878 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (17 : ZMod 1286790383690297300900279) ^ 1451920186 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1454422506018493323437381 : Nat.Prime 1454422506018493323437381 := by
  apply lucas_primality 1454422506018493323437381 (2 : ZMod 1454422506018493323437381)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (109, 1), (18031521274714769693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (109, 1), (18031521274714769693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454422506018493323437381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_37
      · exact prime_fiftySevenBC_109
      · exact prime_fiftySevenBC_18031521274714769693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1454422506018493323437381) ^ 727211253009246661718690 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454422506018493323437381) ^ 290884501203698664687476 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454422506018493323437381) ^ 39308716378878197930740 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454422506018493323437381) ^ 13343325743288929572820 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454422506018493323437381) ^ 80660 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2532667332902167380041627 : Nat.Prime 2532667332902167380041627 := by
  apply lucas_primality 2532667332902167380041627 (2 : ZMod 2532667332902167380041627)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (28631, 1), (1531447, 1), (58110321197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (28631, 1), (1531447, 1), (58110321197, 1)] : List FactorBlock).map factorBlockValue).prod) = 2532667332902167380041627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_71
      · exact prime_fiftySevenBC_28631
      · exact prime_fiftySevenBC_1531447
      · exact prime_fiftySevenBC_58110321197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2532667332902167380041627) ^ 1266333666451083690020813 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532667332902167380041627) ^ 361809618986023911434518 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532667332902167380041627) ^ 35671370885946019437206 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532667332902167380041627) ^ 88458919803784966646 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532667332902167380041627) ^ 1653774066554159158 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532667332902167380041627) ^ 43583777902658 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_2588607244415198772640403 : Nat.Prime 2588607244415198772640403 := by
  apply lucas_primality 2588607244415198772640403 (2 : ZMod 2588607244415198772640403)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (29, 1), (53, 1), (4029173908681858297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (29, 1), (53, 1), (4029173908681858297, 1)] : List FactorBlock).map factorBlockValue).prod) = 2588607244415198772640403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_11
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_4029173908681858297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2588607244415198772640403) ^ 1294303622207599386320201 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588607244415198772640403) ^ 235327931310472615694582 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588607244415198772640403) ^ 136242486548168356454758 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588607244415198772640403) ^ 89262318772937888711738 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588607244415198772640403) ^ 48841646121041486276234 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2588607244415198772640403) ^ 642466 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3573886953429193341543679 : Nat.Prime 3573886953429193341543679 := by
  apply lucas_primality 3573886953429193341543679 (3 : ZMod 3573886953429193341543679)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (3746212739443598890507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (3746212739443598890507, 1)] : List FactorBlock).map factorBlockValue).prod) = 3573886953429193341543679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_53
      · exact prime_fiftySevenBC_3746212739443598890507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3573886953429193341543679) ^ 1786943476714596670771839 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3573886953429193341543679) ^ 1191295651143064447181226 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3573886953429193341543679) ^ 67431829309984780029126 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3573886953429193341543679) ^ 954 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_6182496549895492628270423 : Nat.Prime 6182496549895492628270423 := by
  apply lucas_primality 6182496549895492628270423 (5 : ZMod 6182496549895492628270423)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331139989, 1), (9335170555156799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331139989, 1), (9335170555156799, 1)] : List FactorBlock).map factorBlockValue).prod) = 6182496549895492628270423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_331139989
      · exact prime_fiftySevenBC_9335170555156799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6182496549895492628270423) ^ 3091248274947746314135211 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182496549895492628270423) ^ 18670341110313598 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182496549895492628270423) ^ 662279978 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9787830413051687675838433 : Nat.Prime 9787830413051687675838433 := by
  apply lucas_primality 9787830413051687675838433 (11 : ZMod 9787830413051687675838433)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (13, 1), (382661, 1), (2927922712259267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (13, 1), (382661, 1), (2927922712259267, 1)] : List FactorBlock).map factorBlockValue).prod) = 9787830413051687675838433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_382661
      · exact prime_fiftySevenBC_2927922712259267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9787830413051687675838433) ^ 4893915206525843837919216 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9787830413051687675838433) ^ 3262610137683895891946144 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9787830413051687675838433) ^ 1398261487578812525119776 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9787830413051687675838433) ^ 752910031773206744295264 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9787830413051687675838433) ^ 25578332814296956512 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 9787830413051687675838433) ^ 3342926496 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_11452959278358407486088989 : Nat.Prime 11452959278358407486088989 := by
  apply lucas_primality 11452959278358407486088989 (2 : ZMod 11452959278358407486088989)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (98732407572055236949043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (98732407572055236949043, 1)] : List FactorBlock).map factorBlockValue).prod) = 11452959278358407486088989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_98732407572055236949043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11452959278358407486088989) ^ 5726479639179203743044494 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11452959278358407486088989) ^ 394929630288220947796172 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11452959278358407486088989) ^ 116 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_12351395233478898395921483 : Nat.Prime 12351395233478898395921483 := by
  apply lucas_primality 12351395233478898395921483 (2 : ZMod 12351395233478898395921483)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1193, 1), (5176611581508339646237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1193, 1), (5176611581508339646237, 1)] : List FactorBlock).map factorBlockValue).prod) = 12351395233478898395921483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_1193
      · exact prime_fiftySevenBC_5176611581508339646237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12351395233478898395921483) ^ 6175697616739449197960741 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12351395233478898395921483) ^ 10353223163016679292474 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12351395233478898395921483) ^ 2386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_22568389951058563177544411 : Nat.Prime 22568389951058563177544411 := by
  apply lucas_primality 22568389951058563177544411 (11 : ZMod 22568389951058563177544411)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (409, 1), (7109, 1), (33747446612775307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (409, 1), (7109, 1), (33747446612775307, 1)] : List FactorBlock).map factorBlockValue).prod) = 22568389951058563177544411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_409
      · exact prime_fiftySevenBC_7109
      · exact prime_fiftySevenBC_33747446612775307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22568389951058563177544411) ^ 11284194975529281588772205 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 22568389951058563177544411) ^ 4513677990211712635508882 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 22568389951058563177544411) ^ 981234345698198399023670 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 22568389951058563177544411) ^ 55179437533150521216490 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 22568389951058563177544411) ^ 3174622302863773129490 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (11 : ZMod 22568389951058563177544411) ^ 668743630 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_49550891466074168858932067 : Nat.Prime 49550891466074168858932067 := by
  apply lucas_primality 49550891466074168858932067 (2 : ZMod 49550891466074168858932067)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (73, 1), (113, 1), (15875137, 1), (6102966657511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (73, 1), (113, 1), (15875137, 1), (6102966657511, 1)] : List FactorBlock).map factorBlockValue).prod) = 49550891466074168858932067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_31
      · exact prime_fiftySevenBC_73
      · exact prime_fiftySevenBC_113
      · exact prime_fiftySevenBC_15875137
      · exact prime_fiftySevenBC_6102966657511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49550891466074168858932067) ^ 24775445733037084429466033 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49550891466074168858932067) ^ 1598415853744328027707486 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49550891466074168858932067) ^ 678779335151700943273042 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49550891466074168858932067) ^ 438503464301541317335682 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49550891466074168858932067) ^ 3121289061384110818 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49550891466074168858932067) ^ 8119148317006 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_123649930997909852565408461 : Nat.Prime 123649930997909852565408461 := by
  apply lucas_primality 123649930997909852565408461 (2 : ZMod 123649930997909852565408461)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6182496549895492628270423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6182496549895492628270423, 1)] : List FactorBlock).map factorBlockValue).prod) = 123649930997909852565408461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_6182496549895492628270423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 123649930997909852565408461) ^ 61824965498954926282704230 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 123649930997909852565408461) ^ 24729986199581970513081692 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 123649930997909852565408461) ^ 20 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_208635332488733342563924493 : Nat.Prime 208635332488733342563924493 := by
  apply lucas_primality 208635332488733342563924493 (2 : ZMod 208635332488733342563924493)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2377, 1), (38261, 1), (573511814021432159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2377, 1), (38261, 1), (573511814021432159, 1)] : List FactorBlock).map factorBlockValue).prod) = 208635332488733342563924493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_2377
      · exact prime_fiftySevenBC_38261
      · exact prime_fiftySevenBC_573511814021432159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 208635332488733342563924493) ^ 104317666244366671281962246 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 208635332488733342563924493) ^ 87772542065096063341996 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 208635332488733342563924493) ^ 5452950327715776967772 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 208635332488733342563924493) ^ 363785588 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_302193777550945603803352517 : Nat.Prime 302193777550945603803352517 := by
  apply lucas_primality 302193777550945603803352517 (3 : ZMod 302193777550945603803352517)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (587, 1), (137322883, 1), (7046815021853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (587, 1), (137322883, 1), (7046815021853, 1)] : List FactorBlock).map factorBlockValue).prod) = 302193777550945603803352517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_587
      · exact prime_fiftySevenBC_137322883
      · exact prime_fiftySevenBC_7046815021853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 302193777550945603803352517) ^ 151096888775472801901676258 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 302193777550945603803352517) ^ 43170539650135086257621788 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 302193777550945603803352517) ^ 15904935660576084410702764 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 302193777550945603803352517) ^ 514810523936874963889868 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 302193777550945603803352517) ^ 2200607582284342252 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 302193777550945603803352517) ^ 42883739194772 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_396407131728593350871456537 : Nat.Prime 396407131728593350871456537 := by
  apply lucas_primality 396407131728593350871456537 (3 : ZMod 396407131728593350871456537)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (49550891466074168858932067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (49550891466074168858932067, 1)] : List FactorBlock).map factorBlockValue).prod) = 396407131728593350871456537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_49550891466074168858932067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 396407131728593350871456537) ^ 198203565864296675435728268 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 396407131728593350871456537) ^ 8 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_575976174306503159385877019 : Nat.Prime 575976174306503159385877019 := by
  apply lucas_primality 575976174306503159385877019 (2 : ZMod 575976174306503159385877019)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (67, 1), (812689, 1), (21413042834880569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (67, 1), (812689, 1), (21413042834880569, 1)] : List FactorBlock).map factorBlockValue).prod) = 575976174306503159385877019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_13
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_67
      · exact prime_fiftySevenBC_812689
      · exact prime_fiftySevenBC_21413042834880569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 575976174306503159385877019) ^ 287988087153251579692938509 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 575976174306503159385877019) ^ 44305859562038704568144386 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 575976174306503159385877019) ^ 30314535489815955757151422 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 575976174306503159385877019) ^ 8596659318007509841580254 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 575976174306503159385877019) ^ 708728891748877072762 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 575976174306503159385877019) ^ 26898380522 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_629805723307110931291099171 : Nat.Prime 629805723307110931291099171 := by
  apply lucas_primality 629805723307110931291099171 (10 : ZMod 629805723307110931291099171)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (193, 1), (63389, 1), (1715987573908275307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (193, 1), (63389, 1), (1715987573908275307, 1)] : List FactorBlock).map factorBlockValue).prod) = 629805723307110931291099171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_193
      · exact prime_fiftySevenBC_63389
      · exact prime_fiftySevenBC_1715987573908275307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 629805723307110931291099171) ^ 314902861653555465645549585 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 629805723307110931291099171) ^ 209935241102370310430366390 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 629805723307110931291099171) ^ 125961144661422186258219834 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 629805723307110931291099171) ^ 3263242089674149903062690 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 629805723307110931291099171) ^ 9935568052928914027530 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (10 : ZMod 629805723307110931291099171) ^ 367022310 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_923139895806313282851337141 : Nat.Prime 923139895806313282851337141 := by
  apply lucas_primality 923139895806313282851337141 (2 : ZMod 923139895806313282851337141)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (269, 1), (120871, 1), (29036411, 1), (857719609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (269, 1), (120871, 1), (29036411, 1), (857719609, 1)] : List FactorBlock).map factorBlockValue).prod) = 923139895806313282851337141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_269
      · exact prime_fiftySevenBC_120871
      · exact prime_fiftySevenBC_29036411
      · exact prime_fiftySevenBC_857719609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 923139895806313282851337141) ^ 461569947903156641425668570 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 307713298602104427617112380 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 184627979161262656570267428 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 48586310305595435939544060 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 3431746824558785438109060 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 7637397686842280471340 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 31792493080715563740 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 923139895806313282851337141) ^ 1076272346020613460 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_1142190040573913044883857817 : Nat.Prime 1142190040573913044883857817 := by
  apply lucas_primality 1142190040573913044883857817 (3 : ZMod 1142190040573913044883857817)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (163, 1), (46100663568530555573291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (163, 1), (46100663568530555573291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1142190040573913044883857817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_19
      · exact prime_fiftySevenBC_163
      · exact prime_fiftySevenBC_46100663568530555573291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1142190040573913044883857817) ^ 571095020286956522441928908 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142190040573913044883857817) ^ 60115265293363844467571464 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142190040573913044883857817) ^ 7007300862416644447140232 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1142190040573913044883857817) ^ 24776 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_3209010113993374745149886251 : Nat.Prime 3209010113993374745149886251 := by
  apply lucas_primality 3209010113993374745149886251 (2 : ZMod 3209010113993374745149886251)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) = 3209010113993374745149886251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_179
      · exact prime_fiftySevenBC_449
      · exact prime_fiftySevenBC_261688584010339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3209010113993374745149886251) ^ 1604505056996687372574943125 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 1069670037997791581716628750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 641802022798674949029977250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 139522178869277162832603750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 110655521172185336039651250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 52606723180219258117211250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 17927430804432261146088750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 7147015844083239966926250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3209010113993374745149886251) ^ 12262705788750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_4492614159590724643209840751 : Nat.Prime 4492614159590724643209840751 := by
  apply lucas_primality 4492614159590724643209840751 (3 : ZMod 4492614159590724643209840751)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) = 4492614159590724643209840751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_7
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_179
      · exact prime_fiftySevenBC_449
      · exact prime_fiftySevenBC_261688584010339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4492614159590724643209840751) ^ 2246307079795362321604920375 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 1497538053196908214403280250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 898522831918144928641968150 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 641802022798674949029977250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 195331050416988027965645250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 154917729641059470455511750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 73649412452306961364095750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 25098403126205165604524250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 10005822181716535953696750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4492614159590724643209840751) ^ 17167788104250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_9627030341980124235449658751 : Nat.Prime 9627030341980124235449658751 := by
  apply lucas_primality 9627030341980124235449658751 (7 : ZMod 9627030341980124235449658751)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 4), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 4), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) = 9627030341980124235449658751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_3
      · exact prime_fiftySevenBC_5
      · exact prime_fiftySevenBC_23
      · exact prime_fiftySevenBC_29
      · exact prime_fiftySevenBC_61
      · exact prime_fiftySevenBC_179
      · exact prime_fiftySevenBC_449
      · exact prime_fiftySevenBC_261688584010339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9627030341980124235449658751) ^ 4813515170990062117724829375 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 3209010113993374745149886250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 1925406068396024847089931750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 418566536607831488497811250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 331966563516556008118953750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 157820169540657774351633750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 53782292413296783438266250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 21441047532249719900778750 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (7 : ZMod 9627030341980124235449658751) ^ 36788117366250 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_16847303098465217412036902807 : Nat.Prime 16847303098465217412036902807 := by
  apply lucas_primality 16847303098465217412036902807 (5 : ZMod 16847303098465217412036902807)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2357, 1), (3573886953429193341543679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2357, 1), (3573886953429193341543679, 1)] : List FactorBlock).map factorBlockValue).prod) = 16847303098465217412036902807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_2357
      · exact prime_fiftySevenBC_3573886953429193341543679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16847303098465217412036902807) ^ 8423651549232608706018451403 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16847303098465217412036902807) ^ 7147773906858386683087358 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16847303098465217412036902807) ^ 4714 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_67389212393860869648147611219 : Nat.Prime 67389212393860869648147611219 := by
  apply lucas_primality 67389212393860869648147611219 (2 : ZMod 67389212393860869648147611219)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23399, 1), (258847, 1), (366839267, 1), (15165060059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23399, 1), (258847, 1), (366839267, 1), (15165060059, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_23399
      · exact prime_fiftySevenBC_258847
      · exact prime_fiftySevenBC_366839267
      · exact prime_fiftySevenBC_15165060059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67389212393860869648147611219) ^ 33694606196930434824073805609 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611219) ^ 2880003948624337349807582 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611219) ^ 260343803072320210966894 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611219) ^ 183702287230502152454 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611219) ^ 4443715496785482902 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem prime_fiftySevenBC_67389212393860869648147611267 : Nat.Prime 67389212393860869648147611267 := by
  apply lucas_primality 67389212393860869648147611267 (2 : ZMod 67389212393860869648147611267)
  · rw [← fiftySevenBCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (80407, 1), (24656131, 1), (51346826078279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (80407, 1), (24656131, 1), (51346826078279, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySevenBC_2
      · exact prime_fiftySevenBC_331
      · exact prime_fiftySevenBC_80407
      · exact prime_fiftySevenBC_24656131
      · exact prime_fiftySevenBC_51346826078279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67389212393860869648147611267) ^ 33694606196930434824073805633 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611267) ^ 203592786688401418876578886 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611267) ^ 838101314485814290399438 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611267) ^ 2733162489843230864086 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide
    · change (2 : ZMod 67389212393860869648147611267) ^ 1312431897759854 ≠ 1
      rw [← fiftySevenBCFastPow_eq_pow]
      decide

private theorem phi_fiftySevenBC_67389212393860869648147611200 : Nat.totient 67389212393860869648147611200 = 26955239413187095462163496960 := by
  rw [← show ((([(2, 6), (5, 2), (87679, 1), (224443, 1), (1498309, 1), (1428457609, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_87679, prime_fiftySevenBC_224443, prime_fiftySevenBC_1498309, prime_fiftySevenBC_1428457609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611201 : Nat.totient 67389212393860869648147611201 = 53385944287094247875963523840 := by
  rw [← show ((([(7, 1), (19, 2), (41, 1), (37117, 1), (17523805131372495379, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_7, prime_fiftySevenBC_19, prime_fiftySevenBC_41, prime_fiftySevenBC_37117, prime_fiftySevenBC_17523805131372495379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611202 : Nat.totient 67389212393860869648147611202 = 22462648250018145071860386720 := by
  rw [← show ((([(2, 1), (3, 1), (53161, 1), (211273967739072094355347, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_53161, prime_fiftySevenBC_211273967739072094355347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611203 : Nat.totient 67389212393860869648147611203 = 66247022353286956603263753328 := by
  rw [← show ((([(59, 1), (1142190040573913044883857817, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_59, prime_fiftySevenBC_1142190040573913044883857817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611204 : Nat.totient 67389212393860869648147611204 = 28888503846766923645361152000 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (101, 1), (337, 1), (827, 1), (12390029, 1), (190932896527, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_11, prime_fiftySevenBC_23, prime_fiftySevenBC_101, prime_fiftySevenBC_337, prime_fiftySevenBC_827, prime_fiftySevenBC_12390029, prime_fiftySevenBC_190932896527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611205 : Nat.totient 67389212393860869648147611205 = 33826741907506632607697620992 := by
  rw [← show ((([(3, 4), (5, 1), (17, 1), (9787830413051687675838433, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_17, prime_fiftySevenBC_9787830413051687675838433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611206 : Nat.totient 67389212393860869648147611206 = 32583410456278266171832320000 := by
  rw [← show ((([(2, 1), (47, 1), (97, 1), (601, 1), (4497817, 1), (2734100908328701, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_47, prime_fiftySevenBC_97, prime_fiftySevenBC_601, prime_fiftySevenBC_4497817, prime_fiftySevenBC_2734100908328701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611207 : Nat.totient 67389212393860869648147611207 = 65499129474392711437074432000 := by
  rw [← show ((([(37, 1), (1201, 1), (5381, 1), (34369, 1), (843043, 1), (9726711493, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_37, prime_fiftySevenBC_1201, prime_fiftySevenBC_5381, prime_fiftySevenBC_34369, prime_fiftySevenBC_843043, prime_fiftySevenBC_9726711493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611208 : Nat.totient 67389212393860869648147611208 = 19254059710224840789690816000 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (19773401, 1), (20286154326672070381, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_7, prime_fiftySevenBC_19773401, prime_fiftySevenBC_20286154326672070381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611209 : Nat.totient 67389212393860869648147611209 = 67385685253979683267011584640 := by
  rw [← show ((([(25561, 1), (75653, 1), (34848684271648693373, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_25561, prime_fiftySevenBC_75653, prime_fiftySevenBC_34848684271648693373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611210 : Nat.totient 67389212393860869648147611210 = 24846533688957933623895014400 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (1031, 1), (2161, 1), (232666360355967705187, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_13, prime_fiftySevenBC_1031, prime_fiftySevenBC_2161, prime_fiftySevenBC_232666360355967705187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611211 : Nat.totient 67389212393860869648147611211 = 44926141595905555725097223880 := by
  rw [← show ((([(3, 1), (27464700324307, 1), (817888800267491, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_27464700324307, prime_fiftySevenBC_817888800267491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611212 : Nat.totient 67389212393860869648147611212 = 33562137131239131585647769600 := by
  rw [← show ((([(2, 2), (397, 1), (1091, 1), (3527, 1), (4621, 1), (7501433, 1), (318148199, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_397, prime_fiftySevenBC_1091, prime_fiftySevenBC_3527, prime_fiftySevenBC_4621, prime_fiftySevenBC_7501433, prime_fiftySevenBC_318148199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611213 : Nat.totient 67389212393860869648147611213 = 66646549303746112683261789120 := by
  rw [← show ((([(131, 1), (293, 1), (4691472503, 1), (374233179466837, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_131, prime_fiftySevenBC_293, prime_fiftySevenBC_4691472503, prime_fiftySevenBC_374233179466837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611214 : Nat.totient 67389212393860869648147611214 = 22463070634094920389382717440 := by
  rw [← show ((([(2, 1), (3, 2), (163768879, 1), (869270081, 1), (26298547777, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_163768879, prime_fiftySevenBC_869270081, prime_fiftySevenBC_26298547777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611215 : Nat.totient 67389212393860869648147611215 = 42008716452457391528566080000 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (293413, 1), (867240343, 1), (687877060501, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_7, prime_fiftySevenBC_11, prime_fiftySevenBC_293413, prime_fiftySevenBC_867240343, prime_fiftySevenBC_687877060501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611216 : Nat.totient 67389212393860869648147611216 = 33674344858267217485033459296 := by
  rw [← show ((([(2, 4), (1663, 1), (2532667332902167380041627, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_1663, prime_fiftySevenBC_2532667332902167380041627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611217 : Nat.totient 67389212393860869648147611217 = 43153789194946773377912908800 := by
  rw [← show ((([(3, 1), (31, 1), (137, 1), (7477, 1), (707390925388477988681, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_31, prime_fiftySevenBC_137, prime_fiftySevenBC_7477, prime_fiftySevenBC_707390925388477988681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611218 : Nat.totient 67389212393860869648147611218 = 33693035934549108454685883024 := by
  rw [← show ((([(2, 1), (23399, 1), (258847, 1), (366839267, 1), (15165060059, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_23399, prime_fiftySevenBC_258847, prime_fiftySevenBC_366839267, prime_fiftySevenBC_15165060059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611219 : Nat.totient 67389212393860869648147611219 = 67389212393860869648147611218 := by
  rw [← show ((([(67389212393860869648147611219, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_67389212393860869648147611219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611220 : Nat.totient 67389212393860869648147611220 = 16728868173607424973257932800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (73, 1), (269, 1), (120871, 1), (29036411, 1), (857719609, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_19, prime_fiftySevenBC_73, prime_fiftySevenBC_269, prime_fiftySevenBC_120871, prime_fiftySevenBC_29036411, prime_fiftySevenBC_857719609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611221 : Nat.totient 67389212393860869648147611221 = 64157565462093977378820037632 := by
  rw [← show ((([(29, 1), (79, 1), (797, 1), (17669, 1), (2011573, 1), (1038386902379, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_29, prime_fiftySevenBC_79, prime_fiftySevenBC_797, prime_fiftySevenBC_17669, prime_fiftySevenBC_2011573, prime_fiftySevenBC_1038386902379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611222 : Nat.totient 67389212393860869648147611222 = 26854706892602220744225079296 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (83, 1), (66326046337, 1), (51434109035839, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_7, prime_fiftySevenBC_17, prime_fiftySevenBC_83, prime_fiftySevenBC_66326046337, prime_fiftySevenBC_51434109035839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611223 : Nat.totient 67389212393860869648147611223 = 41470284550068227475783145296 := by
  rw [← show ((([(3, 2), (13, 1), (575976174306503159385877019, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_13, prime_fiftySevenBC_575976174306503159385877019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611224 : Nat.totient 67389212393860869648147611224 = 33680310649116718050707621472 := by
  rw [← show ((([(2, 3), (2357, 1), (3573886953429193341543679, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_2357, prime_fiftySevenBC_3573886953429193341543679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611225 : Nat.totient 67389212393860869648147611225 = 53907942836404915665373366400 := by
  rw [← show ((([(5, 2), (15731, 1), (226978987523, 1), (754932959273, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_15731, prime_fiftySevenBC_226978987523, prime_fiftySevenBC_754932959273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611226 : Nat.totient 67389212393860869648147611226 = 19826629565626527584450791680 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (167, 1), (114662002717, 1), (1240057991093, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_11, prime_fiftySevenBC_43, prime_fiftySevenBC_167, prime_fiftySevenBC_114662002717, prime_fiftySevenBC_1240057991093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611227 : Nat.totient 67389212393860869648147611227 = 64459203808039950843971009280 := by
  rw [← show ((([(23, 1), (1505183, 1), (15343491811, 1), (126867106273, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_23, prime_fiftySevenBC_1505183, prime_fiftySevenBC_15343491811, prime_fiftySevenBC_126867106273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611228 : Nat.totient 67389212393860869648147611228 = 33694606196930434824073805612 := by
  rw [← show ((([(2, 2), (16847303098465217412036902807, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_16847303098465217412036902807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611229 : Nat.totient 67389212393860869648147611229 = 38119919291412032905863782400 := by
  rw [← show ((([(3, 1), (7, 1), (113, 1), (821, 1), (40841, 1), (846940923146321293, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_7, prime_fiftySevenBC_113, prime_fiftySevenBC_821, prime_fiftySevenBC_40841, prime_fiftySevenBC_846940923146321293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611230 : Nat.totient 67389212393860869648147611230 = 26950537796009586670055422432 := by
  rw [← show ((([(2, 1), (5, 1), (5237, 1), (1286790383690297300900279, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_5237, prime_fiftySevenBC_1286790383690297300900279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611231 : Nat.totient 67389212393860869648147611231 = 67380955049978562923956827648 := by
  rw [← show ((([(8237, 1), (886799, 1), (912840689, 1), (10106508133, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_8237, prime_fiftySevenBC_886799, prime_fiftySevenBC_912840689, prime_fiftySevenBC_10106508133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611232 : Nat.totient 67389212393860869648147611232 = 22366347808745592939126177792 := by
  rw [← show ((([(2, 5), (3, 3), (233, 1), (128903, 1), (158129, 1), (16422760812103, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_233, prime_fiftySevenBC_128903, prime_fiftySevenBC_158129, prime_fiftySevenBC_16422760812103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611233 : Nat.totient 67389212393860869648147611233 = 66439863955022959643388975360 := by
  rw [← show ((([(71, 1), (324733, 1), (24850327889, 1), (117617916979, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_71, prime_fiftySevenBC_324733, prime_fiftySevenBC_24850327889, prime_fiftySevenBC_117617916979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611234 : Nat.totient 67389212393860869648147611234 = 33694606195656203246965222000 := by
  rw [← show ((([(2, 1), (26443079501, 1), (1274231550665504117, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_26443079501, prime_fiftySevenBC_1274231550665504117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611235 : Nat.totient 67389212393860869648147611235 = 35936108983983651233265305600 := by
  rw [← show ((([(3, 1), (5, 1), (7481, 1), (568809563981, 1), (1055777924009, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_7481, prime_fiftySevenBC_568809563981, prime_fiftySevenBC_1055777924009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611236 : Nat.totient 67389212393860869648147611236 = 26156459796988441189712961024 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 1), (299303753789, 1), (11670809055547, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_7, prime_fiftySevenBC_13, prime_fiftySevenBC_53, prime_fiftySevenBC_299303753789, prime_fiftySevenBC_11670809055547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611237 : Nat.totient 67389212393860869648147611237 = 61022593690741844596696896000 := by
  rw [← show ((([(11, 1), (461, 1), (569, 1), (52875133, 1), (441705727692511, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_11, prime_fiftySevenBC_461, prime_fiftySevenBC_569, prime_fiftySevenBC_52875133, prime_fiftySevenBC_441705727692511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611238 : Nat.totient 67389212393860869648147611238 = 22432808068733904453393551616 := by
  rw [← show ((([(2, 1), (3, 1), (743, 1), (752929, 1), (20076883162360473959, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_743, prime_fiftySevenBC_752929, prime_fiftySevenBC_20076883162360473959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611239 : Nat.totient 67389212393860869648147611239 = 60086975756755202658410253696 := by
  rw [← show ((([(17, 1), (19, 1), (208635332488733342563924493, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_17, prime_fiftySevenBC_19, prime_fiftySevenBC_208635332488733342563924493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611240 : Nat.totient 67389212393860869648147611240 = 26553238062429793812664258560 := by
  rw [← show ((([(2, 3), (5, 1), (67, 1), (215471, 1), (9039637757, 1), (12909687569, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_67, prime_fiftySevenBC_215471, prime_fiftySevenBC_9039637757, prime_fiftySevenBC_12909687569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611241 : Nat.totient 67389212393860869648147611241 = 44918265596558809003419634560 := by
  rw [← show ((([(3, 2), (5807, 1), (322111, 1), (4003045154941350737, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_5807, prime_fiftySevenBC_322111, prime_fiftySevenBC_4003045154941350737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611242 : Nat.totient 67389212393860869648147611242 = 32783176924341206721920939520 := by
  rw [← show ((([(2, 1), (41, 1), (419, 1), (2957, 1), (513319, 1), (1292182458631453, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_41, prime_fiftySevenBC_419, prime_fiftySevenBC_2957, prime_fiftySevenBC_513319, prime_fiftySevenBC_1292182458631453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611243 : Nat.totient 67389212393860869648147611243 = 57307361642457992412866442000 := by
  rw [← show ((([(7, 2), (127, 1), (731842651, 1), (14796972392894591, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_7, prime_fiftySevenBC_127, prime_fiftySevenBC_731842651, prime_fiftySevenBC_14796972392894591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611244 : Nat.totient 67389212393860869648147611244 = 21854506976597389946085527040 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (15139, 1), (2160841, 1), (4639673395012399, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_37, prime_fiftySevenBC_15139, prime_fiftySevenBC_2160841, prime_fiftySevenBC_4639673395012399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611245 : Nat.totient 67389212393860869648147611245 = 53416770191097056308256454720 := by
  rw [← show ((([(5, 1), (109, 1), (123649930997909852565408461, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_109, prime_fiftySevenBC_123649930997909852565408461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611246 : Nat.totient 67389212393860869648147611246 = 33672037806979376260896259720 := by
  rw [← show ((([(2, 1), (1493, 1), (22568389951058563177544411, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_1493, prime_fiftySevenBC_22568389951058563177544411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611247 : Nat.totient 67389212393860869648147611247 = 44924892848519638309072708032 := by
  rw [← show ((([(3, 1), (35977, 1), (37525608139, 1), (16638586949783, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_35977, prime_fiftySevenBC_37525608139, prime_fiftySevenBC_16638586949783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611248 : Nat.totient 67389212393860869648147611248 = 29643348560349356150211556800 := by
  rw [← show ((([(2, 4), (11, 1), (31, 1), (12351395233478898395921483, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_11, prime_fiftySevenBC_31, prime_fiftySevenBC_12351395233478898395921483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611249 : Nat.totient 67389212393860869648147611249 = 62205426825004870513418779920 := by
  rw [← show ((([(13, 1), (638246313631, 1), (8121920108347883, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_13, prime_fiftySevenBC_638246313631, prime_fiftySevenBC_8121920108347883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611250 : Nat.totient 67389212393860869648147611250 = 13883125871252191369052160000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 4), (7, 1), (23, 1), (29, 1), (61, 1), (179, 1), (449, 1), (261688584010339, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_7, prime_fiftySevenBC_23, prime_fiftySevenBC_29, prime_fiftySevenBC_61, prime_fiftySevenBC_179, prime_fiftySevenBC_449, prime_fiftySevenBC_261688584010339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611251 : Nat.totient 67389212393860869648147611251 = 67320607020911018104690103040 := by
  rw [← show ((([(1321, 1), (6653, 1), (9013, 1), (850747474409188379, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_1321, prime_fiftySevenBC_6653, prime_fiftySevenBC_9013, prime_fiftySevenBC_850747474409188379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611252 : Nat.totient 67389212393860869648147611252 = 33670987911016343622855108320 := by
  rw [← show ((([(2, 2), (1427, 1), (5530571, 1), (2134698004544397389, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_1427, prime_fiftySevenBC_5530571, prime_fiftySevenBC_2134698004544397389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611253 : Nat.totient 67389212393860869648147611253 = 43970213758100843908103647680 := by
  rw [← show ((([(3, 1), (47, 1), (837773, 1), (570485891228536547821, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_47, prime_fiftySevenBC_837773, prime_fiftySevenBC_570485891228536547821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611254 : Nat.totient 67389212393860869648147611254 = 33693151774424416330750345080 := by
  rw [← show ((([(2, 1), (23167, 1), (1454422506018493323437381, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_23167, prime_fiftySevenBC_1454422506018493323437381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611255 : Nat.totient 67389212393860869648147611255 = 53507427392333064773671845888 := by
  rw [← show ((([(5, 1), (139, 1), (3329, 1), (4900517, 1), (29776049, 1), (199610237, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_139, prime_fiftySevenBC_3329, prime_fiftySevenBC_4900517, prime_fiftySevenBC_29776049, prime_fiftySevenBC_199610237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611256 : Nat.totient 67389212393860869648147611256 = 21138601412831687828598632448 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (6793, 1), (24314682499668368839949, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_17, prime_fiftySevenBC_6793, prime_fiftySevenBC_24314682499668368839949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611257 : Nat.totient 67389212393860869648147611257 = 57762182051880745412697952500 := by
  rw [← show ((([(7, 1), (9627030341980124235449658751, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_7, prime_fiftySevenBC_9627030341980124235449658751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611258 : Nat.totient 67389212393860869648147611258 = 31921141336918722251355193344 := by
  rw [← show ((([(2, 1), (19, 1), (495617, 1), (251641417, 1), (14219308195319, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_19, prime_fiftySevenBC_495617, prime_fiftySevenBC_251641417, prime_fiftySevenBC_14219308195319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611259 : Nat.totient 67389212393860869648147611259 = 40841931048546969258109264800 := by
  rw [← show ((([(3, 3), (11, 1), (3288611, 1), (11880919, 1), (5807261613383, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_11, prime_fiftySevenBC_3288611, prime_fiftySevenBC_11880919, prime_fiftySevenBC_5807261613383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611260 : Nat.totient 67389212393860869648147611260 = 26820321351447562898803261440 := by
  rw [← show ((([(2, 2), (5, 1), (257, 1), (881, 1), (778079567, 1), (19126140539917, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_257, prime_fiftySevenBC_881, prime_fiftySevenBC_778079567, prime_fiftySevenBC_19126140539917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611261 : Nat.totient 67389212393860869648147611261 = 67389212393860349813604598524 := by
  rw [← show ((([(246964448128639, 1), (272870094884099, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_246964448128639, prime_fiftySevenBC_272870094884099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611262 : Nat.totient 67389212393860869648147611262 = 20383686112216242022534037376 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (1726787, 1), (16063259, 1), (527923912507, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_13, prime_fiftySevenBC_59, prime_fiftySevenBC_1726787, prime_fiftySevenBC_16063259, prime_fiftySevenBC_527923912507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611263 : Nat.totient 67389212393860869648147611263 = 67092582175954342217328888000 := by
  rw [← show ((([(359, 1), (617, 1), (13859729371, 1), (21951086332051, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_359, prime_fiftySevenBC_617, prime_fiftySevenBC_13859729371, prime_fiftySevenBC_21951086332051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611264 : Nat.totient 67389212393860869648147611264 = 28682399418251984874860802048 := by
  rw [← show ((([(2, 7), (7, 1), (173, 1), (907, 1), (316907, 1), (1512506147720767, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_7, prime_fiftySevenBC_173, prime_fiftySevenBC_907, prime_fiftySevenBC_316907, prime_fiftySevenBC_1512506147720767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611265 : Nat.totient 67389212393860869648147611265 = 35940913276725797145678726000 := by
  rw [← show ((([(3, 1), (5, 1), (4492614159590724643209840751, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_4492614159590724643209840751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611266 : Nat.totient 67389212393860869648147611266 = 33592390656506750977959877200 := by
  rw [← show ((([(2, 1), (331, 1), (80407, 1), (24656131, 1), (51346826078279, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_331, prime_fiftySevenBC_80407, prime_fiftySevenBC_24656131, prime_fiftySevenBC_51346826078279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611267 : Nat.totient 67389212393860869648147611267 = 67389212393860869648147611266 := by
  rw [← show ((([(67389212393860869648147611267, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_67389212393860869648147611267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611268 : Nat.totient 67389212393860869648147611268 = 22463070797951484360385428480 := by
  rw [← show ((([(2, 2), (3, 2), (11207041479521, 1), (167030930501753, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_11207041479521, prime_fiftySevenBC_167030930501753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611269 : Nat.totient 67389212393860869648147611269 = 65822021342579317300317987840 := by
  rw [← show ((([(43, 1), (1006794511, 1), (1556614551212765953, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_43, prime_fiftySevenBC_1006794511, prime_fiftySevenBC_1556614551212765953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611270 : Nat.totient 67389212393860869648147611270 = 24504784087905693515034344000 := by
  rw [← show ((([(2, 1), (5, 1), (11, 2), (87887, 1), (232871, 1), (2721228194211431, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_11, prime_fiftySevenBC_87887, prime_fiftySevenBC_232871, prime_fiftySevenBC_2721228194211431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611271 : Nat.totient 67389212393860869648147611271 = 38508121367920496941798635000 := by
  rw [← show ((([(3, 1), (7, 1), (3209010113993374745149886251, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_7, prime_fiftySevenBC_3209010113993374745149886251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611272 : Nat.totient 67389212393860869648147611272 = 33694606196802139727938040064 := by
  rw [← show ((([(2, 3), (262635775817, 1), (32073511398165577, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_262635775817, prime_fiftySevenBC_32073511398165577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611273 : Nat.totient 67389212393860869648147611273 = 60650475438663596550942535680 := by
  rw [← show ((([(17, 1), (23, 1), (3643, 1), (154417, 1), (12492211, 1), (24525621983, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_17, prime_fiftySevenBC_23, prime_fiftySevenBC_3643, prime_fiftySevenBC_154417, prime_fiftySevenBC_12492211, prime_fiftySevenBC_24525621983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611274 : Nat.totient 67389212393860869648147611274 = 22463010302517894819986833536 := by
  rw [← show ((([(2, 1), (3, 1), (435143, 1), (2857507, 1), (23557913, 1), (383427283, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_435143, prime_fiftySevenBC_2857507, prime_fiftySevenBC_23557913, prime_fiftySevenBC_383427283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611275 : Nat.totient 67389212393860869648147611275 = 49205191556036009229692985600 := by
  rw [← show ((([(5, 2), (13, 2), (89, 1), (179214712835212737579011, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_13, prime_fiftySevenBC_89, prime_fiftySevenBC_179214712835212737579011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611276 : Nat.totient 67389212393860869648147611276 = 33671700278373718009101624720 := by
  rw [← show ((([(2, 2), (1471, 1), (11452959278358407486088989, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_1471, prime_fiftySevenBC_11452959278358407486088989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611277 : Nat.totient 67389212393860869648147611277 = 42509892629855062877107287168 := by
  rw [← show ((([(3, 2), (19, 1), (823, 1), (478844424504990795677969, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_19, prime_fiftySevenBC_823, prime_fiftySevenBC_478844424504990795677969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611278 : Nat.totient 67389212393860869648147611278 = 28848857157319170555695554560 := by
  rw [← show ((([(2, 1), (7, 1), (1097, 1), (4889, 1), (6336409, 1), (141642139437641, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_7, prime_fiftySevenBC_1097, prime_fiftySevenBC_4889, prime_fiftySevenBC_6336409, prime_fiftySevenBC_141642139437641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611279 : Nat.totient 67389212393860869648147611279 = 62966248016559472239980613120 := by
  rw [← show ((([(29, 1), (31, 1), (240209, 1), (1236307, 1), (252414956818967, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_29, prime_fiftySevenBC_31, prime_fiftySevenBC_240209, prime_fiftySevenBC_1236307, prime_fiftySevenBC_252414956818967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611280 : Nat.totient 67389212393860869648147611280 = 17938729943840111043950395392 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (857, 1), (1669, 1), (5918687, 1), (33167795470157, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_857, prime_fiftySevenBC_1669, prime_fiftySevenBC_5918687, prime_fiftySevenBC_33167795470157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611281 : Nat.totient 67389212393860869648147611281 = 59592812956828650009659203200 := by
  rw [← show ((([(11, 1), (37, 1), (4153, 1), (39868880430333875247311, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_11, prime_fiftySevenBC_37, prime_fiftySevenBC_4153, prime_fiftySevenBC_39868880430333875247311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611282 : Nat.totient 67389212393860869648147611282 = 33694606195695567221744224384 := by
  rw [← show ((([(2, 1), (27286007729, 1), (1234867575043573529, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_27286007729, prime_fiftySevenBC_1234867575043573529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611283 : Nat.totient 67389212393860869648147611283 = 43830382044614236715576668160 := by
  rw [← show ((([(3, 1), (41, 1), (252915429737, 1), (2166256823988833, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_41, prime_fiftySevenBC_252915429737, prime_fiftySevenBC_2166256823988833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611284 : Nat.totient 67389212393860869648147611284 = 33690914840709142118676249600 := by
  rw [← show ((([(2, 2), (9133, 1), (16587401, 1), (111208654882691537, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_9133, prime_fiftySevenBC_16587401, prime_fiftySevenBC_111208654882691537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611285 : Nat.totient 67389212393860869648147611285 = 46063973572849046129820820992 := by
  rw [← show ((([(5, 1), (7, 1), (317, 1), (119674037227, 1), (50753165169689, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_5, prime_fiftySevenBC_7, prime_fiftySevenBC_317, prime_fiftySevenBC_119674037227, prime_fiftySevenBC_50753165169689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611286 : Nat.totient 67389212393860869648147611286 = 22463049851158484936971485792 := by
  rw [← show ((([(2, 1), (3, 4), (1072387, 1), (387903613671833700169, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_1072387, prime_fiftySevenBC_387903613671833700169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611287 : Nat.totient 67389212393860869648147611287 = 67389053147491250977637632440 := by
  rw [← show ((([(423179, 1), (57405551891, 1), (2774037809383, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_423179, prime_fiftySevenBC_57405551891, prime_fiftySevenBC_2774037809383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611288 : Nat.totient 67389212393860869648147611288 = 31102713411419708819330976000 := by
  rw [← show ((([(2, 3), (13, 1), (27488997001, 1), (23572093084052647, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_13, prime_fiftySevenBC_27488997001, prime_fiftySevenBC_23572093084052647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611289 : Nat.totient 67389212393860869648147611289 = 43834200217838743971996840960 := by
  rw [← show ((([(3, 1), (53, 1), (199, 1), (1931, 1), (660337, 1), (1670291510551507, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_53, prime_fiftySevenBC_199, prime_fiftySevenBC_1931, prime_fiftySevenBC_660337, prime_fiftySevenBC_1670291510551507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611290 : Nat.totient 67389212393860869648147611290 = 25370056430629974455773218304 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (396407131728593350871456537, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_17, prime_fiftySevenBC_396407131728593350871456537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611291 : Nat.totient 67389212393860869648147611291 = 67087018616309924044344258552 := by
  rw [← show ((([(223, 1), (302193777550945603803352517, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_223, prime_fiftySevenBC_302193777550945603803352517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611292 : Nat.totient 67389212393860869648147611292 = 17503286699558780734605425280 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (11, 1), (43237, 1), (240971020340726598187, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_7, prime_fiftySevenBC_11, prime_fiftySevenBC_43237, prime_fiftySevenBC_240971020340726598187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611293 : Nat.totient 67389212393860869648147611293 = 66466072498054556365296274080 := by
  rw [← show ((([(73, 1), (923139895806313282851337141, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_73, prime_fiftySevenBC_923139895806313282851337141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611294 : Nat.totient 67389212393860869648147611294 = 33627416080072564381544514432 := by
  rw [← show ((([(2, 1), (503, 1), (179563, 1), (2162059, 1), (172547235718097, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_503, prime_fiftySevenBC_179563, prime_fiftySevenBC_2162059, prime_fiftySevenBC_172547235718097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611295 : Nat.totient 67389212393860869648147611295 = 35570004480080340799909637376 := by
  rw [← show ((([(3, 2), (5, 1), (103, 1), (1667, 1), (57653, 1), (151280562751723667, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_3, prime_fiftySevenBC_5, prime_fiftySevenBC_103, prime_fiftySevenBC_1667, prime_fiftySevenBC_57653, prime_fiftySevenBC_151280562751723667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611296 : Nat.totient 67389212393860869648147611296 = 30495578225982754455029200896 := by
  rw [← show ((([(2, 5), (19, 1), (23, 1), (809, 1), (4314803, 1), (1380541516990147, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_19, prime_fiftySevenBC_23, prime_fiftySevenBC_809, prime_fiftySevenBC_4314803, prime_fiftySevenBC_1380541516990147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611297 : Nat.totient 67389212393860869648147611297 = 66759406670553758716856512020 := by
  rw [← show ((([(107, 1), (629805723307110931291099171, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_107, prime_fiftySevenBC_629805723307110931291099171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611298 : Nat.totient 67389212393860869648147611298 = 22370739527136899103166241280 := by
  rw [← show ((([(2, 1), (3, 1), (277, 1), (2003, 1), (355513, 1), (56940716243176861, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_3, prime_fiftySevenBC_277, prime_fiftySevenBC_2003, prime_fiftySevenBC_355513, prime_fiftySevenBC_56940716243176861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611299 : Nat.totient 67389212393860869648147611299 = 57746650408414254220062087816 := by
  rw [← show ((([(7, 1), (3719, 1), (2588607244415198772640403, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_7, prime_fiftySevenBC_3719, prime_fiftySevenBC_2588607244415198772640403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySevenBC_67389212393860869648147611300 : Nat.totient 67389212393860869648147611300 = 26048208356370074897560512000 := by
  rw [← show ((([(2, 2), (5, 2), (47, 1), (79, 1), (335591012221, 1), (540822946981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67389212393860869648147611300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySevenBC_2, prime_fiftySevenBC_5, prime_fiftySevenBC_47, prime_fiftySevenBC_79, prime_fiftySevenBC_335591012221, prime_fiftySevenBC_540822946981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftySevenBC : certifiedKill 1 67389212393860869648147611199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftySevenBC_67389212393860869648147611200, phi_fiftySevenBC_67389212393860869648147611201, phi_fiftySevenBC_67389212393860869648147611202,
    phi_fiftySevenBC_67389212393860869648147611203, phi_fiftySevenBC_67389212393860869648147611204, phi_fiftySevenBC_67389212393860869648147611205,
    phi_fiftySevenBC_67389212393860869648147611206, phi_fiftySevenBC_67389212393860869648147611207, phi_fiftySevenBC_67389212393860869648147611208,
    phi_fiftySevenBC_67389212393860869648147611209, phi_fiftySevenBC_67389212393860869648147611210, phi_fiftySevenBC_67389212393860869648147611211,
    phi_fiftySevenBC_67389212393860869648147611212, phi_fiftySevenBC_67389212393860869648147611213, phi_fiftySevenBC_67389212393860869648147611214,
    phi_fiftySevenBC_67389212393860869648147611215, phi_fiftySevenBC_67389212393860869648147611216, phi_fiftySevenBC_67389212393860869648147611217,
    phi_fiftySevenBC_67389212393860869648147611218, phi_fiftySevenBC_67389212393860869648147611219, phi_fiftySevenBC_67389212393860869648147611220,
    phi_fiftySevenBC_67389212393860869648147611221, phi_fiftySevenBC_67389212393860869648147611222, phi_fiftySevenBC_67389212393860869648147611223,
    phi_fiftySevenBC_67389212393860869648147611224, phi_fiftySevenBC_67389212393860869648147611225, phi_fiftySevenBC_67389212393860869648147611226,
    phi_fiftySevenBC_67389212393860869648147611227, phi_fiftySevenBC_67389212393860869648147611228, phi_fiftySevenBC_67389212393860869648147611229,
    phi_fiftySevenBC_67389212393860869648147611230, phi_fiftySevenBC_67389212393860869648147611231, phi_fiftySevenBC_67389212393860869648147611232,
    phi_fiftySevenBC_67389212393860869648147611233, phi_fiftySevenBC_67389212393860869648147611234, phi_fiftySevenBC_67389212393860869648147611235,
    phi_fiftySevenBC_67389212393860869648147611236, phi_fiftySevenBC_67389212393860869648147611237, phi_fiftySevenBC_67389212393860869648147611238,
    phi_fiftySevenBC_67389212393860869648147611239, phi_fiftySevenBC_67389212393860869648147611240, phi_fiftySevenBC_67389212393860869648147611241,
    phi_fiftySevenBC_67389212393860869648147611242, phi_fiftySevenBC_67389212393860869648147611243, phi_fiftySevenBC_67389212393860869648147611244,
    phi_fiftySevenBC_67389212393860869648147611245, phi_fiftySevenBC_67389212393860869648147611246, phi_fiftySevenBC_67389212393860869648147611247,
    phi_fiftySevenBC_67389212393860869648147611248, phi_fiftySevenBC_67389212393860869648147611249, phi_fiftySevenBC_67389212393860869648147611250,
    phi_fiftySevenBC_67389212393860869648147611251, phi_fiftySevenBC_67389212393860869648147611252, phi_fiftySevenBC_67389212393860869648147611253,
    phi_fiftySevenBC_67389212393860869648147611254, phi_fiftySevenBC_67389212393860869648147611255, phi_fiftySevenBC_67389212393860869648147611256,
    phi_fiftySevenBC_67389212393860869648147611257, phi_fiftySevenBC_67389212393860869648147611258, phi_fiftySevenBC_67389212393860869648147611259,
    phi_fiftySevenBC_67389212393860869648147611260, phi_fiftySevenBC_67389212393860869648147611261, phi_fiftySevenBC_67389212393860869648147611262,
    phi_fiftySevenBC_67389212393860869648147611263, phi_fiftySevenBC_67389212393860869648147611264, phi_fiftySevenBC_67389212393860869648147611265,
    phi_fiftySevenBC_67389212393860869648147611266, phi_fiftySevenBC_67389212393860869648147611267, phi_fiftySevenBC_67389212393860869648147611268,
    phi_fiftySevenBC_67389212393860869648147611269, phi_fiftySevenBC_67389212393860869648147611270, phi_fiftySevenBC_67389212393860869648147611271,
    phi_fiftySevenBC_67389212393860869648147611272, phi_fiftySevenBC_67389212393860869648147611273, phi_fiftySevenBC_67389212393860869648147611274,
    phi_fiftySevenBC_67389212393860869648147611275, phi_fiftySevenBC_67389212393860869648147611276, phi_fiftySevenBC_67389212393860869648147611277,
    phi_fiftySevenBC_67389212393860869648147611278, phi_fiftySevenBC_67389212393860869648147611279, phi_fiftySevenBC_67389212393860869648147611280,
    phi_fiftySevenBC_67389212393860869648147611281, phi_fiftySevenBC_67389212393860869648147611282, phi_fiftySevenBC_67389212393860869648147611283,
    phi_fiftySevenBC_67389212393860869648147611284, phi_fiftySevenBC_67389212393860869648147611285, phi_fiftySevenBC_67389212393860869648147611286,
    phi_fiftySevenBC_67389212393860869648147611287, phi_fiftySevenBC_67389212393860869648147611288, phi_fiftySevenBC_67389212393860869648147611289,
    phi_fiftySevenBC_67389212393860869648147611290, phi_fiftySevenBC_67389212393860869648147611291, phi_fiftySevenBC_67389212393860869648147611292,
    phi_fiftySevenBC_67389212393860869648147611293, phi_fiftySevenBC_67389212393860869648147611294, phi_fiftySevenBC_67389212393860869648147611295,
    phi_fiftySevenBC_67389212393860869648147611296, phi_fiftySevenBC_67389212393860869648147611297, phi_fiftySevenBC_67389212393860869648147611298,
    phi_fiftySevenBC_67389212393860869648147611299, phi_fiftySevenBC_67389212393860869648147611300
  ]

end TotientTailPeriodKiller
end Erdos249257
