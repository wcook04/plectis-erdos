import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 49P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyNineAUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyNineAUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyNineAUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyNineAUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyNineAUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyNineAUFastPow a n * fortyNineAUFastPow a n * a
        else fortyNineAUFastPow a n * fortyNineAUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyNineAU_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyNineAU_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyNineAU_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyNineAU_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyNineAU_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyNineAU_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyNineAU_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyNineAU_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyNineAU_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyNineAU_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyNineAU_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyNineAU_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyNineAU_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyNineAU_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyNineAU_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyNineAU_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyNineAU_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyNineAU_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyNineAU_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyNineAU_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyNineAU_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyNineAU_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyNineAU_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyNineAU_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyNineAU_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyNineAU_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyNineAU_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyNineAU_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyNineAU_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyNineAU_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyNineAU_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyNineAU_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyNineAU_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyNineAU_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyNineAU_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyNineAU_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyNineAU_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyNineAU_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyNineAU_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyNineAU_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyNineAU_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyNineAU_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyNineAU_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyNineAU_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyNineAU_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyNineAU_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyNineAU_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyNineAU_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyNineAU_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyNineAU_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortyNineAU_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyNineAU_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyNineAU_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyNineAU_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyNineAU_313 : Nat.Prime 313 := by norm_num
private theorem prime_fortyNineAU_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyNineAU_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyNineAU_337 : Nat.Prime 337 := by norm_num
private theorem prime_fortyNineAU_347 : Nat.Prime 347 := by norm_num
private theorem prime_fortyNineAU_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyNineAU_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyNineAU_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyNineAU_373 : Nat.Prime 373 := by norm_num
private theorem prime_fortyNineAU_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyNineAU_389 : Nat.Prime 389 := by norm_num
private theorem prime_fortyNineAU_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyNineAU_401 : Nat.Prime 401 := by norm_num
private theorem prime_fortyNineAU_409 : Nat.Prime 409 := by norm_num
private theorem prime_fortyNineAU_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortyNineAU_431 : Nat.Prime 431 := by norm_num
private theorem prime_fortyNineAU_443 : Nat.Prime 443 := by norm_num
private theorem prime_fortyNineAU_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortyNineAU_467 : Nat.Prime 467 := by norm_num
private theorem prime_fortyNineAU_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyNineAU_509 : Nat.Prime 509 := by norm_num
private theorem prime_fortyNineAU_541 : Nat.Prime 541 := by norm_num
private theorem prime_fortyNineAU_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortyNineAU_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyNineAU_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyNineAU_601 : Nat.Prime 601 := by norm_num
private theorem prime_fortyNineAU_631 : Nat.Prime 631 := by norm_num
private theorem prime_fortyNineAU_653 : Nat.Prime 653 := by norm_num
private theorem prime_fortyNineAU_659 : Nat.Prime 659 := by norm_num
private theorem prime_fortyNineAU_673 : Nat.Prime 673 := by norm_num
private theorem prime_fortyNineAU_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortyNineAU_683 : Nat.Prime 683 := by norm_num
private theorem prime_fortyNineAU_691 : Nat.Prime 691 := by norm_num
private theorem prime_fortyNineAU_701 : Nat.Prime 701 := by norm_num
private theorem prime_fortyNineAU_751 : Nat.Prime 751 := by norm_num
private theorem prime_fortyNineAU_757 : Nat.Prime 757 := by norm_num
private theorem prime_fortyNineAU_809 : Nat.Prime 809 := by norm_num
private theorem prime_fortyNineAU_821 : Nat.Prime 821 := by norm_num
private theorem prime_fortyNineAU_839 : Nat.Prime 839 := by norm_num
private theorem prime_fortyNineAU_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortyNineAU_863 : Nat.Prime 863 := by norm_num
private theorem prime_fortyNineAU_887 : Nat.Prime 887 := by norm_num
private theorem prime_fortyNineAU_907 : Nat.Prime 907 := by norm_num
private theorem prime_fortyNineAU_937 : Nat.Prime 937 := by norm_num
private theorem prime_fortyNineAU_947 : Nat.Prime 947 := by norm_num
private theorem prime_fortyNineAU_953 : Nat.Prime 953 := by norm_num
private theorem prime_fortyNineAU_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortyNineAU_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyNineAU_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fortyNineAU_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fortyNineAU_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_fortyNineAU_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fortyNineAU_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortyNineAU_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_fortyNineAU_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fortyNineAU_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_fortyNineAU_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_fortyNineAU_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortyNineAU_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_fortyNineAU_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fortyNineAU_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_fortyNineAU_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyNineAU_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_fortyNineAU_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_fortyNineAU_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_fortyNineAU_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyNineAU_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_fortyNineAU_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_fortyNineAU_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_fortyNineAU_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fortyNineAU_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_fortyNineAU_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_fortyNineAU_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_fortyNineAU_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_fortyNineAU_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_fortyNineAU_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fortyNineAU_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_fortyNineAU_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_fortyNineAU_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_fortyNineAU_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_fortyNineAU_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fortyNineAU_2437 : Nat.Prime 2437 := by norm_num
private theorem prime_fortyNineAU_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_fortyNineAU_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyNineAU_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_fortyNineAU_2683 : Nat.Prime 2683 := by norm_num
private theorem prime_fortyNineAU_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_fortyNineAU_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_fortyNineAU_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_fortyNineAU_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_fortyNineAU_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_fortyNineAU_2953 : Nat.Prime 2953 := by norm_num
private theorem prime_fortyNineAU_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_fortyNineAU_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fortyNineAU_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_fortyNineAU_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_fortyNineAU_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_fortyNineAU_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_fortyNineAU_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_fortyNineAU_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_fortyNineAU_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_fortyNineAU_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_fortyNineAU_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_fortyNineAU_4441 : Nat.Prime 4441 := by norm_num
private theorem prime_fortyNineAU_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_fortyNineAU_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_fortyNineAU_4639 : Nat.Prime 4639 := by norm_num
private theorem prime_fortyNineAU_4759 : Nat.Prime 4759 := by norm_num
private theorem prime_fortyNineAU_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_fortyNineAU_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyNineAU_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_fortyNineAU_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_fortyNineAU_5273 : Nat.Prime 5273 := by norm_num
private theorem prime_fortyNineAU_5303 : Nat.Prime 5303 := by norm_num
private theorem prime_fortyNineAU_5381 : Nat.Prime 5381 := by norm_num
private theorem prime_fortyNineAU_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_fortyNineAU_5503 : Nat.Prime 5503 := by norm_num
private theorem prime_fortyNineAU_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_fortyNineAU_5821 : Nat.Prime 5821 := by norm_num
private theorem prime_fortyNineAU_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_fortyNineAU_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_fortyNineAU_6143 : Nat.Prime 6143 := by norm_num
private theorem prime_fortyNineAU_6301 : Nat.Prime 6301 := by norm_num
private theorem prime_fortyNineAU_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_fortyNineAU_6571 : Nat.Prime 6571 := by norm_num
private theorem prime_fortyNineAU_6661 : Nat.Prime 6661 := by norm_num
private theorem prime_fortyNineAU_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyNineAU_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_fortyNineAU_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_fortyNineAU_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_fortyNineAU_7951 : Nat.Prime 7951 := by norm_num
private theorem prime_fortyNineAU_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_fortyNineAU_9601 : Nat.Prime 9601 := by norm_num
private theorem prime_fortyNineAU_9649 : Nat.Prime 9649 := by norm_num
private theorem prime_fortyNineAU_9941 : Nat.Prime 9941 := by norm_num
private theorem prime_fortyNineAU_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_fortyNineAU_10477 : Nat.Prime 10477 := by norm_num
private theorem prime_fortyNineAU_11399 : Nat.Prime 11399 := by norm_num
private theorem prime_fortyNineAU_11801 : Nat.Prime 11801 := by norm_num
private theorem prime_fortyNineAU_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_fortyNineAU_12953 : Nat.Prime 12953 := by norm_num
private theorem prime_fortyNineAU_13327 : Nat.Prime 13327 := by norm_num
private theorem prime_fortyNineAU_13829 : Nat.Prime 13829 := by norm_num
private theorem prime_fortyNineAU_13967 : Nat.Prime 13967 := by norm_num
private theorem prime_fortyNineAU_14087 : Nat.Prime 14087 := by norm_num
private theorem prime_fortyNineAU_14519 : Nat.Prime 14519 := by norm_num
private theorem prime_fortyNineAU_15013 : Nat.Prime 15013 := by norm_num
private theorem prime_fortyNineAU_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_fortyNineAU_17053 : Nat.Prime 17053 := by norm_num
private theorem prime_fortyNineAU_17827 : Nat.Prime 17827 := by norm_num
private theorem prime_fortyNineAU_19181 : Nat.Prime 19181 := by norm_num
private theorem prime_fortyNineAU_19373 : Nat.Prime 19373 := by norm_num
private theorem prime_fortyNineAU_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_fortyNineAU_19441 : Nat.Prime 19441 := by norm_num
private theorem prime_fortyNineAU_20173 : Nat.Prime 20173 := by norm_num
private theorem prime_fortyNineAU_22109 : Nat.Prime 22109 := by norm_num
private theorem prime_fortyNineAU_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_fortyNineAU_22567 : Nat.Prime 22567 := by norm_num
private theorem prime_fortyNineAU_22727 : Nat.Prime 22727 := by norm_num
private theorem prime_fortyNineAU_25889 : Nat.Prime 25889 := by norm_num
private theorem prime_fortyNineAU_26449 : Nat.Prime 26449 := by norm_num
private theorem prime_fortyNineAU_27143 : Nat.Prime 27143 := by norm_num
private theorem prime_fortyNineAU_28057 : Nat.Prime 28057 := by norm_num
private theorem prime_fortyNineAU_28081 : Nat.Prime 28081 := by norm_num
private theorem prime_fortyNineAU_29741 : Nat.Prime 29741 := by norm_num
private theorem prime_fortyNineAU_31723 : Nat.Prime 31723 := by norm_num
private theorem prime_fortyNineAU_33811 : Nat.Prime 33811 := by norm_num
private theorem prime_fortyNineAU_34183 : Nat.Prime 34183 := by norm_num
private theorem prime_fortyNineAU_34543 : Nat.Prime 34543 := by norm_num
private theorem prime_fortyNineAU_34549 : Nat.Prime 34549 := by norm_num
private theorem prime_fortyNineAU_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyNineAU_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyNineAU_39181 : Nat.Prime 39181 := by norm_num
private theorem prime_fortyNineAU_40883 : Nat.Prime 40883 := by norm_num
private theorem prime_fortyNineAU_40973 : Nat.Prime 40973 := by norm_num
private theorem prime_fortyNineAU_42643 : Nat.Prime 42643 := by norm_num
private theorem prime_fortyNineAU_43591 : Nat.Prime 43591 := by norm_num
private theorem prime_fortyNineAU_43609 : Nat.Prime 43609 := by norm_num
private theorem prime_fortyNineAU_44711 : Nat.Prime 44711 := by norm_num
private theorem prime_fortyNineAU_44893 : Nat.Prime 44893 := by norm_num
private theorem prime_fortyNineAU_49297 : Nat.Prime 49297 := by norm_num
private theorem prime_fortyNineAU_50383 : Nat.Prime 50383 := by norm_num
private theorem prime_fortyNineAU_50741 : Nat.Prime 50741 := by norm_num
private theorem prime_fortyNineAU_56737 : Nat.Prime 56737 := by norm_num
private theorem prime_fortyNineAU_58031 : Nat.Prime 58031 := by norm_num
private theorem prime_fortyNineAU_58169 : Nat.Prime 58169 := by norm_num
private theorem prime_fortyNineAU_60647 : Nat.Prime 60647 := by norm_num
private theorem prime_fortyNineAU_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyNineAU_66587 : Nat.Prime 66587 := by norm_num
private theorem prime_fortyNineAU_67211 : Nat.Prime 67211 := by norm_num
private theorem prime_fortyNineAU_70201 : Nat.Prime 70201 := by norm_num
private theorem prime_fortyNineAU_72497 : Nat.Prime 72497 := by norm_num
private theorem prime_fortyNineAU_72973 : Nat.Prime 72973 := by norm_num
private theorem prime_fortyNineAU_73061 : Nat.Prime 73061 := by norm_num
private theorem prime_fortyNineAU_73523 : Nat.Prime 73523 := by norm_num
private theorem prime_fortyNineAU_77153 : Nat.Prime 77153 := by norm_num
private theorem prime_fortyNineAU_79693 : Nat.Prime 79693 := by norm_num
private theorem prime_fortyNineAU_80737 : Nat.Prime 80737 := by norm_num
private theorem prime_fortyNineAU_81409 : Nat.Prime 81409 := by norm_num
private theorem prime_fortyNineAU_82217 : Nat.Prime 82217 := by norm_num
private theorem prime_fortyNineAU_87383 : Nat.Prime 87383 := by norm_num
private theorem prime_fortyNineAU_89153 : Nat.Prime 89153 := by norm_num
private theorem prime_fortyNineAU_89819 : Nat.Prime 89819 := by norm_num
private theorem prime_fortyNineAU_93901 : Nat.Prime 93901 := by norm_num
private theorem prime_fortyNineAU_94709 : Nat.Prime 94709 := by norm_num
private theorem prime_fortyNineAU_99581 : Nat.Prime 99581 := by norm_num
private theorem prime_fortyNineAU_99689 : Nat.Prime 99689 := by norm_num
private theorem prime_fortyNineAU_101641 : Nat.Prime 101641 := by norm_num
private theorem prime_fortyNineAU_103919 : Nat.Prime 103919 := by norm_num
private theorem prime_fortyNineAU_103991 : Nat.Prime 103991 := by norm_num
private theorem prime_fortyNineAU_104579 : Nat.Prime 104579 := by norm_num
private theorem prime_fortyNineAU_112291 : Nat.Prime 112291 := by norm_num
private theorem prime_fortyNineAU_127487 : Nat.Prime 127487 := by norm_num
private theorem prime_fortyNineAU_130043 : Nat.Prime 130043 := by norm_num
private theorem prime_fortyNineAU_132491 : Nat.Prime 132491 := by norm_num
private theorem prime_fortyNineAU_134873 : Nat.Prime 134873 := by norm_num
private theorem prime_fortyNineAU_135497 : Nat.Prime 135497 := by norm_num
private theorem prime_fortyNineAU_135929 : Nat.Prime 135929 := by norm_num
private theorem prime_fortyNineAU_136013 : Nat.Prime 136013 := by norm_num
private theorem prime_fortyNineAU_144899 : Nat.Prime 144899 := by norm_num
private theorem prime_fortyNineAU_148859 : Nat.Prime 148859 := by norm_num
private theorem prime_fortyNineAU_151517 : Nat.Prime 151517 := by norm_num
private theorem prime_fortyNineAU_154841 : Nat.Prime 154841 := by norm_num
private theorem prime_fortyNineAU_161149 : Nat.Prime 161149 := by norm_num
private theorem prime_fortyNineAU_172517 : Nat.Prime 172517 := by norm_num
private theorem prime_fortyNineAU_175079 : Nat.Prime 175079 := by norm_num
private theorem prime_fortyNineAU_178261 : Nat.Prime 178261 := by norm_num
private theorem prime_fortyNineAU_180629 : Nat.Prime 180629 := by norm_num
private theorem prime_fortyNineAU_189491 : Nat.Prime 189491 := by norm_num
private theorem prime_fortyNineAU_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_fortyNineAU_194863 : Nat.Prime 194863 := by norm_num
private theorem prime_fortyNineAU_195271 : Nat.Prime 195271 := by norm_num
private theorem prime_fortyNineAU_206527 : Nat.Prime 206527 := by norm_num
private theorem prime_fortyNineAU_210283 : Nat.Prime 210283 := by norm_num
private theorem prime_fortyNineAU_214007 : Nat.Prime 214007 := by norm_num
private theorem prime_fortyNineAU_220903 : Nat.Prime 220903 := by norm_num
private theorem prime_fortyNineAU_234893 : Nat.Prime 234893 := by norm_num
private theorem prime_fortyNineAU_242161 : Nat.Prime 242161 := by norm_num
private theorem prime_fortyNineAU_246361 : Nat.Prime 246361 := by norm_num
private theorem prime_fortyNineAU_293147 : Nat.Prime 293147 := by norm_num
private theorem prime_fortyNineAU_293507 : Nat.Prime 293507 := by norm_num
private theorem prime_fortyNineAU_299059 : Nat.Prime 299059 := by norm_num
private theorem prime_fortyNineAU_311677 : Nat.Prime 311677 := by norm_num
private theorem prime_fortyNineAU_312979 : Nat.Prime 312979 := by norm_num
private theorem prime_fortyNineAU_313471 : Nat.Prime 313471 := by norm_num
private theorem prime_fortyNineAU_328249 : Nat.Prime 328249 := by norm_num
private theorem prime_fortyNineAU_330731 : Nat.Prime 330731 := by norm_num
private theorem prime_fortyNineAU_343543 : Nat.Prime 343543 := by norm_num
private theorem prime_fortyNineAU_363611 : Nat.Prime 363611 := by norm_num
private theorem prime_fortyNineAU_367219 : Nat.Prime 367219 := by norm_num
private theorem prime_fortyNineAU_386051 : Nat.Prime 386051 := by norm_num
private theorem prime_fortyNineAU_411583 : Nat.Prime 411583 := by norm_num
private theorem prime_fortyNineAU_412339 : Nat.Prime 412339 := by norm_num
private theorem prime_fortyNineAU_413869 : Nat.Prime 413869 := by norm_num
private theorem prime_fortyNineAU_450829 : Nat.Prime 450829 := by norm_num
private theorem prime_fortyNineAU_454907 : Nat.Prime 454907 := by norm_num
private theorem prime_fortyNineAU_466247 : Nat.Prime 466247 := by norm_num
private theorem prime_fortyNineAU_524701 : Nat.Prime 524701 := by norm_num
private theorem prime_fortyNineAU_527507 : Nat.Prime 527507 := by norm_num
private theorem prime_fortyNineAU_534341 : Nat.Prime 534341 := by norm_num
private theorem prime_fortyNineAU_548771 : Nat.Prime 548771 := by norm_num
private theorem prime_fortyNineAU_600403 : Nat.Prime 600403 := by norm_num
private theorem prime_fortyNineAU_630167 : Nat.Prime 630167 := by norm_num
private theorem prime_fortyNineAU_645493 : Nat.Prime 645493 := by norm_num
private theorem prime_fortyNineAU_659539 : Nat.Prime 659539 := by norm_num
private theorem prime_fortyNineAU_719419 : Nat.Prime 719419 := by norm_num
private theorem prime_fortyNineAU_743573 : Nat.Prime 743573 := by norm_num
private theorem prime_fortyNineAU_753161 : Nat.Prime 753161 := by norm_num
private theorem prime_fortyNineAU_811457 : Nat.Prime 811457 := by norm_num
private theorem prime_fortyNineAU_886793 : Nat.Prime 886793 := by norm_num
private theorem prime_fortyNineAU_918563 : Nat.Prime 918563 := by norm_num
private theorem prime_fortyNineAU_951649 : Nat.Prime 951649 := by norm_num
private theorem prime_fortyNineAU_960151 : Nat.Prime 960151 := by norm_num
private theorem prime_fortyNineAU_1077977 : Nat.Prime 1077977 := by norm_num
private theorem prime_fortyNineAU_1080841 : Nat.Prime 1080841 := by norm_num
private theorem prime_fortyNineAU_1150823 : Nat.Prime 1150823 := by norm_num
private theorem prime_fortyNineAU_1173959 : Nat.Prime 1173959 := by norm_num
private theorem prime_fortyNineAU_1189579 : Nat.Prime 1189579 := by norm_num
private theorem prime_fortyNineAU_1197451 : Nat.Prime 1197451 := by norm_num
private theorem prime_fortyNineAU_1298723 : Nat.Prime 1298723 := by norm_num
private theorem prime_fortyNineAU_1401809 : Nat.Prime 1401809 := by norm_num
private theorem prime_fortyNineAU_1473763 : Nat.Prime 1473763 := by norm_num
private theorem prime_fortyNineAU_1640557 : Nat.Prime 1640557 := by norm_num
private theorem prime_fortyNineAU_1652513 : Nat.Prime 1652513 := by norm_num
private theorem prime_fortyNineAU_1693169 : Nat.Prime 1693169 := by norm_num
private theorem prime_fortyNineAU_1854233 : Nat.Prime 1854233 := by norm_num
private theorem prime_fortyNineAU_1957301 : Nat.Prime 1957301 := by norm_num
private theorem prime_fortyNineAU_2256827 : Nat.Prime 2256827 := by norm_num
private theorem prime_fortyNineAU_2744563 : Nat.Prime 2744563 := by norm_num
private theorem prime_fortyNineAU_2746801 : Nat.Prime 2746801 := by norm_num
private theorem prime_fortyNineAU_2767657 : Nat.Prime 2767657 := by norm_num
private theorem prime_fortyNineAU_2794079 : Nat.Prime 2794079 := by norm_num
private theorem prime_fortyNineAU_2846287 : Nat.Prime 2846287 := by norm_num
private theorem prime_fortyNineAU_2897933 : Nat.Prime 2897933 := by norm_num
private theorem prime_fortyNineAU_3244957 : Nat.Prime 3244957 := by norm_num
private theorem prime_fortyNineAU_3285647 : Nat.Prime 3285647 := by norm_num
private theorem prime_fortyNineAU_3302191 : Nat.Prime 3302191 := by norm_num
private theorem prime_fortyNineAU_3402079 : Nat.Prime 3402079 := by norm_num
private theorem prime_fortyNineAU_3470581 : Nat.Prime 3470581 := by norm_num
private theorem prime_fortyNineAU_3473947 : Nat.Prime 3473947 := by norm_num
private theorem prime_fortyNineAU_3532679 : Nat.Prime 3532679 := by norm_num
private theorem prime_fortyNineAU_3617473 : Nat.Prime 3617473 := by norm_num
private theorem prime_fortyNineAU_3779417 : Nat.Prime 3779417 := by norm_num
private theorem prime_fortyNineAU_3804263 : Nat.Prime 3804263 := by norm_num
private theorem prime_fortyNineAU_3835763 : Nat.Prime 3835763 := by norm_num
private theorem prime_fortyNineAU_4148603 : Nat.Prime 4148603 := by norm_num
private theorem prime_fortyNineAU_4353499 : Nat.Prime 4353499 := by norm_num
private theorem prime_fortyNineAU_4586051 : Nat.Prime 4586051 := by norm_num
private theorem prime_fortyNineAU_5160101 : Nat.Prime 5160101 := by norm_num
private theorem prime_fortyNineAU_5177033 : Nat.Prime 5177033 := by norm_num
private theorem prime_fortyNineAU_6140923 : Nat.Prime 6140923 := by norm_num
private theorem prime_fortyNineAU_6475879 : Nat.Prime 6475879 := by norm_num
private theorem prime_fortyNineAU_6669709 : Nat.Prime 6669709 := by norm_num
private theorem prime_fortyNineAU_6995189 : Nat.Prime 6995189 := by norm_num
private theorem prime_fortyNineAU_7046861 : Nat.Prime 7046861 := by norm_num
private theorem prime_fortyNineAU_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyNineAU_7361537 : Nat.Prime 7361537 := by norm_num
private theorem prime_fortyNineAU_7396243 : Nat.Prime 7396243 := by norm_num
private theorem prime_fortyNineAU_7978459 : Nat.Prime 7978459 := by norm_num
private theorem prime_fortyNineAU_8045381 : Nat.Prime 8045381 := by norm_num
private theorem prime_fortyNineAU_8460433 : Nat.Prime 8460433 := by norm_num
private theorem prime_fortyNineAU_8977307 : Nat.Prime 8977307 := by norm_num
private theorem prime_fortyNineAU_10202561 : Nat.Prime 10202561 := by norm_num
private theorem prime_fortyNineAU_11131361 : Nat.Prime 11131361 := by norm_num
private theorem prime_fortyNineAU_11874781 : Nat.Prime 11874781 := by norm_num
private theorem prime_fortyNineAU_13393859 : Nat.Prime 13393859 := by norm_num
private theorem prime_fortyNineAU_15233941 : Nat.Prime 15233941 := by norm_num
private theorem prime_fortyNineAU_15480197 : Nat.Prime 15480197 := by norm_num
private theorem prime_fortyNineAU_16749767 : Nat.Prime 16749767 := by norm_num
private theorem prime_fortyNineAU_17426659 : Nat.Prime 17426659 := by norm_num
private theorem prime_fortyNineAU_17972329 : Nat.Prime 17972329 := by norm_num
private theorem prime_fortyNineAU_19182841 : Nat.Prime 19182841 := by norm_num
private theorem prime_fortyNineAU_20001521 : Nat.Prime 20001521 := by norm_num
private theorem prime_fortyNineAU_22951043 : Nat.Prime 22951043 := by norm_num
private theorem prime_fortyNineAU_25290107 : Nat.Prime 25290107 := by norm_num
private theorem prime_fortyNineAU_27504469 : Nat.Prime 27504469 := by norm_num
private theorem prime_fortyNineAU_31893469 : Nat.Prime 31893469 := by
  apply lucas_primality 31893469 (6 : ZMod 31893469)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (751, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (751, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) = 31893469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_751
      · exact prime_fortyNineAU_3539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 31893469) ^ 15946734 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31893469) ^ 10631156 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31893469) ^ 42468 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31893469) ^ 9012 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_31990579 : Nat.Prime 31990579 := by
  apply lucas_primality 31990579 (10 : ZMod 31990579)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (130043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (130043, 1)] : List FactorBlock).map factorBlockValue).prod) = 31990579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_130043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 31990579) ^ 15995289 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 31990579) ^ 10663526 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 31990579) ^ 780258 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 31990579) ^ 246 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_37344499 : Nat.Prime 37344499 := by
  apply lucas_primality 37344499 (2 : ZMod 37344499)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (58169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (58169, 1)] : List FactorBlock).map factorBlockValue).prod) = 37344499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_107
      · exact prime_fortyNineAU_58169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37344499) ^ 18672249 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37344499) ^ 12448166 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37344499) ^ 349014 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 37344499) ^ 642 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_37560013 : Nat.Prime 37560013 := by
  apply lucas_primality 37560013 (5 : ZMod 37560013)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (19441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (19441, 1)] : List FactorBlock).map factorBlockValue).prod) = 37560013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_19441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37560013) ^ 18780006 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37560013) ^ 12520004 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37560013) ^ 5365716 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37560013) ^ 1633044 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37560013) ^ 1932 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_38303933 : Nat.Prime 38303933 := by
  apply lucas_primality 38303933 (2 : ZMod 38303933)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (134873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (134873, 1)] : List FactorBlock).map factorBlockValue).prod) = 38303933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_71
      · exact prime_fortyNineAU_134873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38303933) ^ 19151966 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38303933) ^ 539492 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38303933) ^ 284 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_40003043 : Nat.Prime 40003043 := by
  apply lucas_primality 40003043 (2 : ZMod 40003043)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20001521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20001521, 1)] : List FactorBlock).map factorBlockValue).prod) = 40003043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_20001521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 40003043) ^ 20001521 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 40003043) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_42045439 : Nat.Prime 42045439 := by
  apply lucas_primality 42045439 (3 : ZMod 42045439)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (12953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (12953, 1)] : List FactorBlock).map factorBlockValue).prod) = 42045439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_541
      · exact prime_fortyNineAU_12953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42045439) ^ 21022719 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42045439) ^ 14015146 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42045439) ^ 77718 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 42045439) ^ 3246 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_43623427 : Nat.Prime 43623427 := by
  apply lucas_primality 43623427 (3 : ZMod 43623427)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (11, 1), (41, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (11, 1), (41, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 43623427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43623427) ^ 21811713 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 43623427) ^ 14541142 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 43623427) ^ 6231918 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 43623427) ^ 3965766 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 43623427) ^ 1063986 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 43623427) ^ 928158 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_43713101 : Nat.Prime 43713101 := by
  apply lucas_primality 43713101 (7 : ZMod 43713101)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (59, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (59, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 43713101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 43713101) ^ 21856550 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43713101) ^ 8742620 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43713101) ^ 1410100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43713101) ^ 740900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43713101) ^ 182900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_44878781 : Nat.Prime 44878781 := by
  apply lucas_primality 44878781 (2 : ZMod 44878781)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (60647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (60647, 1)] : List FactorBlock).map factorBlockValue).prod) = 44878781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_60647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44878781) ^ 22439390 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878781) ^ 8975756 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878781) ^ 1212940 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878781) ^ 740 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_45547919 : Nat.Prime 45547919 := by
  apply lucas_primality 45547919 (7 : ZMod 45547919)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (263, 1), (6661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (263, 1), (6661, 1)] : List FactorBlock).map factorBlockValue).prod) = 45547919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_263
      · exact prime_fortyNineAU_6661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 45547919) ^ 22773959 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45547919) ^ 3503686 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45547919) ^ 173186 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 45547919) ^ 6838 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_50640673 : Nat.Prime 50640673 := by
  apply lucas_primality 50640673 (7 : ZMod 50640673)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (527507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (527507, 1)] : List FactorBlock).map factorBlockValue).prod) = 50640673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_527507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 50640673) ^ 25320336 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 50640673) ^ 16880224 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 50640673) ^ 96 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_57064603 : Nat.Prime 57064603 := by
  apply lucas_primality 57064603 (2 : ZMod 57064603)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (443, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (443, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 57064603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_443
      · exact prime_fortyNineAU_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57064603) ^ 28532301 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57064603) ^ 19021534 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57064603) ^ 8152086 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57064603) ^ 128814 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57064603) ^ 18606 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_58892297 : Nat.Prime 58892297 := by
  apply lucas_primality 58892297 (3 : ZMod 58892297)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7361537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7361537, 1)] : List FactorBlock).map factorBlockValue).prod) = 58892297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7361537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58892297) ^ 29446148 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 58892297) ^ 8 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_61241107 : Nat.Prime 61241107 := by
  apply lucas_primality 61241107 (3 : ZMod 61241107)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (600403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (600403, 1)] : List FactorBlock).map factorBlockValue).prod) = 61241107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_600403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61241107) ^ 30620553 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61241107) ^ 20413702 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61241107) ^ 3602418 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 61241107) ^ 102 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_64335203 : Nat.Prime 64335203 := by
  apply lucas_primality 64335203 (2 : ZMod 64335203)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (821, 1), (39181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (821, 1), (39181, 1)] : List FactorBlock).map factorBlockValue).prod) = 64335203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_821
      · exact prime_fortyNineAU_39181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64335203) ^ 32167601 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 64335203) ^ 78362 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 64335203) ^ 1642 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_64363049 : Nat.Prime 64363049 := by
  apply lucas_primality 64363049 (3 : ZMod 64363049)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8045381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8045381, 1)] : List FactorBlock).map factorBlockValue).prod) = 64363049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_8045381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 64363049) ^ 32181524 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 64363049) ^ 8 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_68422259 : Nat.Prime 68422259 := by
  apply lucas_primality 68422259 (2 : ZMod 68422259)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (645493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (645493, 1)] : List FactorBlock).map factorBlockValue).prod) = 68422259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_645493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68422259) ^ 34211129 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68422259) ^ 1290986 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68422259) ^ 106 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_71000429 : Nat.Prime 71000429 := by
  apply lucas_primality 71000429 (2 : ZMod 71000429)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (135497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (135497, 1)] : List FactorBlock).map factorBlockValue).prod) = 71000429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_131
      · exact prime_fortyNineAU_135497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71000429) ^ 35500214 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 71000429) ^ 541988 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 71000429) ^ 524 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_76804727 : Nat.Prime 76804727 := by
  apply lucas_primality 76804727 (5 : ZMod 76804727)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (49297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (49297, 1)] : List FactorBlock).map factorBlockValue).prod) = 76804727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_49297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76804727) ^ 38402363 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 76804727) ^ 4042354 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 76804727) ^ 1873286 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 76804727) ^ 1558 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_89497481 : Nat.Prime 89497481 := by
  apply lucas_primality 89497481 (3 : ZMod 89497481)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (77153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (77153, 1)] : List FactorBlock).map factorBlockValue).prod) = 89497481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_77153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89497481) ^ 44748740 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 89497481) ^ 17899496 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 89497481) ^ 3086120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 89497481) ^ 1160 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_91302313 : Nat.Prime 91302313 := by
  apply lucas_primality 91302313 (5 : ZMod 91302313)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3804263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3804263, 1)] : List FactorBlock).map factorBlockValue).prod) = 91302313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_3804263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 91302313) ^ 45651156 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 91302313) ^ 30434104 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 91302313) ^ 24 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_102433609 : Nat.Prime 102433609 := by
  apply lucas_primality 102433609 (7 : ZMod 102433609)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (683, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (683, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 102433609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_683
      · exact prime_fortyNineAU_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 102433609) ^ 51216804 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 102433609) ^ 34144536 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 102433609) ^ 149976 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 102433609) ^ 49176 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_108084101 : Nat.Prime 108084101 := by
  apply lucas_primality 108084101 (2 : ZMod 108084101)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (1080841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (1080841, 1)] : List FactorBlock).map factorBlockValue).prod) = 108084101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_1080841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108084101) ^ 54042050 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 108084101) ^ 21616820 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 108084101) ^ 100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_108506029 : Nat.Prime 108506029 := by
  apply lucas_primality 108506029 (2 : ZMod 108506029)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (210283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (210283, 1)] : List FactorBlock).map factorBlockValue).prod) = 108506029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_210283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108506029) ^ 54253014 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 108506029) ^ 36168676 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 108506029) ^ 2523396 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 108506029) ^ 516 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_119910317 : Nat.Prime 119910317 := by
  apply lucas_primality 119910317 (2 : ZMod 119910317)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (43, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (43, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 119910317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119910317) ^ 59955158 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119910317) ^ 7053548 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119910317) ^ 5213492 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119910317) ^ 2788612 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 119910317) ^ 67252 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_125131961 : Nat.Prime 125131961 := by
  apply lucas_primality 125131961 (6 : ZMod 125131961)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (136013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (136013, 1)] : List FactorBlock).map factorBlockValue).prod) = 125131961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_136013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 125131961) ^ 62565980 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 125131961) ^ 25026392 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 125131961) ^ 5440520 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 125131961) ^ 920 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_131628851 : Nat.Prime 131628851 := by
  apply lucas_primality 131628851 (2 : ZMod 131628851)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (61, 1), (103, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (61, 1), (103, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 131628851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_61
      · exact prime_fortyNineAU_103
      · exact prime_fortyNineAU_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131628851) ^ 65814425 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131628851) ^ 26325770 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131628851) ^ 2157850 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131628851) ^ 1277950 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131628851) ^ 314150 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_132684341 : Nat.Prime 132684341 := by
  apply lucas_primality 132684341 (2 : ZMod 132684341)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (214007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (214007, 1)] : List FactorBlock).map factorBlockValue).prod) = 132684341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_214007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 132684341) ^ 66342170 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132684341) ^ 26536868 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132684341) ^ 4280140 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132684341) ^ 620 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_137106667 : Nat.Prime 137106667 := by
  apply lucas_primality 137106667 (5 : ZMod 137106667)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (167, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (167, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod) = 137106667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_167
      · exact prime_fortyNineAU_2683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137106667) ^ 68553333 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 137106667) ^ 45702222 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 137106667) ^ 8065098 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 137106667) ^ 820998 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 137106667) ^ 51102 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_138875111 : Nat.Prime 138875111 := by
  apply lucas_primality 138875111 (7 : ZMod 138875111)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (701, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (701, 1), (1801, 1)] : List FactorBlock).map factorBlockValue).prod) = 138875111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_701
      · exact prime_fortyNineAU_1801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 138875111) ^ 69437555 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 138875111) ^ 27775022 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 138875111) ^ 12625010 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 138875111) ^ 198110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 138875111) ^ 77110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_144114781 : Nat.Prime 144114781 := by
  apply lucas_primality 144114781 (2 : ZMod 144114781)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (23, 1), (6143, 1)] : List FactorBlock).map factorBlockValue).prod) = 144114781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_6143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144114781) ^ 72057390 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144114781) ^ 48038260 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144114781) ^ 28822956 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144114781) ^ 8477340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144114781) ^ 6265860 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 144114781) ^ 23460 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_155755937 : Nat.Prime 155755937 := by
  apply lucas_primality 155755937 (3 : ZMod 155755937)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (61, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (61, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) = 155755937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_61
      · exact prime_fortyNineAU_11399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 155755937) ^ 77877968 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 155755937) ^ 22250848 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 155755937) ^ 2553376 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 155755937) ^ 13664 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_174266591 : Nat.Prime 174266591 := by
  apply lucas_primality 174266591 (7 : ZMod 174266591)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17426659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17426659, 1)] : List FactorBlock).map factorBlockValue).prod) = 174266591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17426659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 174266591) ^ 87133295 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 174266591) ^ 34853318 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 174266591) ^ 10 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_188446523 : Nat.Prime 188446523 := by
  apply lucas_primality 188446523 (2 : ZMod 188446523)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (450829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (450829, 1)] : List FactorBlock).map factorBlockValue).prod) = 188446523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_450829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188446523) ^ 94223261 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188446523) ^ 17131502 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188446523) ^ 9918238 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188446523) ^ 418 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_189375691 : Nat.Prime 189375691 := by
  apply lucas_primality 189375691 (12 : ZMod 189375691)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (47, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (47, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 189375691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 189375691) ^ 94687845 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (12 : ZMod 189375691) ^ 63125230 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (12 : ZMod 189375691) ^ 37875138 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (12 : ZMod 189375691) ^ 27053670 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (12 : ZMod 189375691) ^ 4029270 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (12 : ZMod 189375691) ^ 69090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_204944669 : Nat.Prime 204944669 := by
  apply lucas_primality 204944669 (2 : ZMod 204944669)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1483, 1), (34549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1483, 1), (34549, 1)] : List FactorBlock).map factorBlockValue).prod) = 204944669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1483
      · exact prime_fortyNineAU_34549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204944669) ^ 102472334 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 204944669) ^ 138196 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 204944669) ^ 5932 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_208360531 : Nat.Prime 208360531 := by
  apply lucas_primality 208360531 (2 : ZMod 208360531)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (330731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (330731, 1)] : List FactorBlock).map factorBlockValue).prod) = 208360531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_330731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 208360531) ^ 104180265 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 208360531) ^ 69453510 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 208360531) ^ 41672106 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 208360531) ^ 29765790 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 208360531) ^ 630 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_244710289 : Nat.Prime 244710289 := by
  apply lucas_primality 244710289 (7 : ZMod 244710289)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (59, 1), (9601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (59, 1), (9601, 1)] : List FactorBlock).map factorBlockValue).prod) = 244710289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_9601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 244710289) ^ 122355144 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 244710289) ^ 81570096 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 244710289) ^ 4147632 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 244710289) ^ 25488 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_269272687 : Nat.Prime 269272687 := by
  apply lucas_primality 269272687 (3 : ZMod 269272687)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (44878781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (44878781, 1)] : List FactorBlock).map factorBlockValue).prod) = 269272687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_44878781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269272687) ^ 134636343 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 269272687) ^ 89757562 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 269272687) ^ 6 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_319905791 : Nat.Prime 319905791 := by
  apply lucas_primality 319905791 (7 : ZMod 319905791)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31990579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31990579, 1)] : List FactorBlock).map factorBlockValue).prod) = 319905791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_31990579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 319905791) ^ 159952895 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 319905791) ^ 63981158 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 319905791) ^ 10 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_330207509 : Nat.Prime 330207509 := by
  apply lucas_primality 330207509 (2 : ZMod 330207509)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (630167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (630167, 1)] : List FactorBlock).map factorBlockValue).prod) = 330207509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_131
      · exact prime_fortyNineAU_630167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 330207509) ^ 165103754 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 330207509) ^ 2520668 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 330207509) ^ 524 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_348533183 : Nat.Prime 348533183 := by
  apply lucas_primality 348533183 (5 : ZMod 348533183)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (174266591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (174266591, 1)] : List FactorBlock).map factorBlockValue).prod) = 348533183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_174266591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 348533183) ^ 174266591 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 348533183) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_358253981 : Nat.Prime 358253981 := by
  apply lucas_primality 358253981 (2 : ZMod 358253981)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (23, 1), (31, 1), (37, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (23, 1), (31, 1), (37, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 358253981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 358253981) ^ 179126990 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 71650796 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 51179140 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 15576260 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 11556580 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 9682540 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 358253981) ^ 3693340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_365209253 : Nat.Prime 365209253 := by
  apply lucas_primality 365209253 (2 : ZMod 365209253)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (91302313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (91302313, 1)] : List FactorBlock).map factorBlockValue).prod) = 365209253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_91302313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 365209253) ^ 182604626 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 365209253) ^ 4 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_368725771 : Nat.Prime 368725771 := by
  apply lucas_primality 368725771 (3 : ZMod 368725771)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (7, 1), (53, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (7, 1), (53, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 368725771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 368725771) ^ 184362885 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 368725771) ^ 122908590 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 368725771) ^ 73745154 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 368725771) ^ 52675110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 368725771) ^ 6957090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 368725771) ^ 901530 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_393736093 : Nat.Prime 393736093 := by
  apply lucas_primality 393736093 (2 : ZMod 393736093)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (886793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (886793, 1)] : List FactorBlock).map factorBlockValue).prod) = 393736093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_886793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 393736093) ^ 196868046 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 393736093) ^ 131245364 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 393736093) ^ 10641516 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 393736093) ^ 444 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_421049003 : Nat.Prime 421049003 := by
  apply lucas_primality 421049003 (2 : ZMod 421049003)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (101, 1), (189491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (101, 1), (189491, 1)] : List FactorBlock).map factorBlockValue).prod) = 421049003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_101
      · exact prime_fortyNineAU_189491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 421049003) ^ 210524501 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 421049003) ^ 38277182 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 421049003) ^ 4168802 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 421049003) ^ 2222 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_434226839 : Nat.Prime 434226839 := by
  apply lucas_primality 434226839 (7 : ZMod 434226839)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2953, 1), (73523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2953, 1), (73523, 1)] : List FactorBlock).map factorBlockValue).prod) = 434226839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_2953
      · exact prime_fortyNineAU_73523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 434226839) ^ 217113419 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 434226839) ^ 147046 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 434226839) ^ 5906 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_441669461 : Nat.Prime 441669461 := by
  apply lucas_primality 441669461 (2 : ZMod 441669461)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (960151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (960151, 1)] : List FactorBlock).map factorBlockValue).prod) = 441669461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_960151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 441669461) ^ 220834730 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 441669461) ^ 88333892 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 441669461) ^ 19203020 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 441669461) ^ 460 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_550326121 : Nat.Prime 550326121 := by
  apply lucas_primality 550326121 (19 : ZMod 550326121)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (4586051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (4586051, 1)] : List FactorBlock).map factorBlockValue).prod) = 550326121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_4586051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 550326121) ^ 275163060 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 550326121) ^ 183442040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 550326121) ^ 110065224 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 550326121) ^ 120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_79
      · exact prime_fortyNineAU_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_622326449 : Nat.Prime 622326449 := by
  apply lucas_primality 622326449 (3 : ZMod 622326449)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (89, 1), (101, 1), (4327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (89, 1), (101, 1), (4327, 1)] : List FactorBlock).map factorBlockValue).prod) = 622326449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_89
      · exact prime_fortyNineAU_101
      · exact prime_fortyNineAU_4327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 622326449) ^ 311163224 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 622326449) ^ 6992432 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 622326449) ^ 6161648 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 622326449) ^ 143824 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_625982537 : Nat.Prime 625982537 := by
  apply lucas_primality 625982537 (3 : ZMod 625982537)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (3402079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (3402079, 1)] : List FactorBlock).map factorBlockValue).prod) = 625982537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_3402079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 625982537) ^ 312991268 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 625982537) ^ 27216632 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 625982537) ^ 184 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_692605391 : Nat.Prime 692605391 := by
  apply lucas_primality 692605391 (7 : ZMod 692605391)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211, 1), (328249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211, 1), (328249, 1)] : List FactorBlock).map factorBlockValue).prod) = 692605391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_211
      · exact prime_fortyNineAU_328249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 692605391) ^ 346302695 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 692605391) ^ 138521078 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 692605391) ^ 3282490 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 692605391) ^ 2110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_697066367 : Nat.Prime 697066367 := by
  apply lucas_primality 697066367 (5 : ZMod 697066367)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (348533183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (348533183, 1)] : List FactorBlock).map factorBlockValue).prod) = 697066367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_348533183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 697066367) ^ 348533183 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 697066367) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_713273257 : Nat.Prime 713273257 := by
  apply lucas_primality 713273257 (5 : ZMod 713273257)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (3302191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (3302191, 1)] : List FactorBlock).map factorBlockValue).prod) = 713273257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_3302191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 713273257) ^ 356636628 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 713273257) ^ 237757752 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 713273257) ^ 216 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_719461903 : Nat.Prime 719461903 := by
  apply lucas_primality 719461903 (17 : ZMod 719461903)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (119910317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (119910317, 1)] : List FactorBlock).map factorBlockValue).prod) = 719461903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_119910317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 719461903) ^ 359730951 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (17 : ZMod 719461903) ^ 239820634 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (17 : ZMod 719461903) ^ 6 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_861821473 : Nat.Prime 861821473 := by
  apply lucas_primality 861821473 (31 : ZMod 861821473)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (8977307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (8977307, 1)] : List FactorBlock).map factorBlockValue).prod) = 861821473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_8977307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (31 : ZMod 861821473) ^ 430910736 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (31 : ZMod 861821473) ^ 287273824 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (31 : ZMod 861821473) ^ 96 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_962488451 : Nat.Prime 962488451 := by
  apply lucas_primality 962488451 (6 : ZMod 962488451)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (11, 2), (22727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (11, 2), (22727, 1)] : List FactorBlock).map factorBlockValue).prod) = 962488451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_22727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 962488451) ^ 481244225 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 962488451) ^ 192497690 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 962488451) ^ 137498350 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 962488451) ^ 87498950 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 962488451) ^ 42350 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1166625463 : Nat.Prime 1166625463 := by
  apply lucas_primality 1166625463 (3 : ZMod 1166625463)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2053, 1), (94709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2053, 1), (94709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166625463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_2053
      · exact prime_fortyNineAU_94709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1166625463) ^ 583312731 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1166625463) ^ 388875154 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1166625463) ^ 568254 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1166625463) ^ 12318 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_113
      · exact prime_fortyNineAU_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1252604263 : Nat.Prime 1252604263 := by
  apply lucas_primality 1252604263 (3 : ZMod 1252604263)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (97, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (97, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252604263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_97
      · exact prime_fortyNineAU_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1252604263) ^ 626302131 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 417534754 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 178943466 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 96354174 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 18695586 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 12913446 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1252604263) ^ 3548454 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1377110333 : Nat.Prime 1377110333 := by
  apply lucas_primality 1377110333 (2 : ZMod 1377110333)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1367, 1), (19373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1367, 1), (19373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1377110333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_1367
      · exact prime_fortyNineAU_19373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1377110333) ^ 688555166 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1377110333) ^ 105931564 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1377110333) ^ 1007396 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1377110333) ^ 71084 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1601286227 : Nat.Prime 1601286227 := by
  apply lucas_primality 1601286227 (2 : ZMod 1601286227)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6043, 1), (132491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6043, 1), (132491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601286227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_6043
      · exact prime_fortyNineAU_132491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1601286227) ^ 800643113 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601286227) ^ 264982 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601286227) ^ 12086 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1924976903 : Nat.Prime 1924976903 := by
  apply lucas_primality 1924976903 (5 : ZMod 1924976903)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (962488451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (962488451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1924976903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_962488451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1924976903) ^ 962488451 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1924976903) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1993429663 : Nat.Prime 1993429663 := by
  apply lucas_primality 1993429663 (3 : ZMod 1993429663)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (467, 1), (14519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (467, 1), (14519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1993429663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_467
      · exact prime_fortyNineAU_14519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1993429663) ^ 996714831 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1993429663) ^ 664476554 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1993429663) ^ 284775666 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1993429663) ^ 4268586 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1993429663) ^ 137298 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2047090049 : Nat.Prime 2047090049 := by
  apply lucas_primality 2047090049 (3 : ZMod 2047090049)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (223, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (223, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2047090049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_223
      · exact prime_fortyNineAU_2473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2047090049) ^ 1023545024 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047090049) ^ 70589312 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047090049) ^ 9179776 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2047090049) ^ 827776 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2316067309 : Nat.Prime 2316067309 := by
  apply lucas_primality 2316067309 (2 : ZMod 2316067309)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (64335203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (64335203, 1)] : List FactorBlock).map factorBlockValue).prod) = 2316067309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_64335203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2316067309) ^ 1158033654 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2316067309) ^ 772022436 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2316067309) ^ 36 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2625921271 : Nat.Prime 2625921271 := by
  apply lucas_primality 2625921271 (14 : ZMod 2625921271)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (23, 1), (25889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (23, 1), (25889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2625921271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_25889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2625921271) ^ 1312960635 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625921271) ^ 875307090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625921271) ^ 525184254 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625921271) ^ 375131610 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625921271) ^ 114170490 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625921271) ^ 101430 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2730396233 : Nat.Prime 2730396233 := by
  apply lucas_primality 2730396233 (3 : ZMod 2730396233)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1453, 1), (234893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1453, 1), (234893, 1)] : List FactorBlock).map factorBlockValue).prod) = 2730396233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1453
      · exact prime_fortyNineAU_234893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2730396233) ^ 1365198116 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2730396233) ^ 1879144 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2730396233) ^ 11624 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2877847613 : Nat.Prime 2877847613 := by
  apply lucas_primality 2877847613 (2 : ZMod 2877847613)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (719461903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (719461903, 1)] : List FactorBlock).map factorBlockValue).prod) = 2877847613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_719461903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2877847613) ^ 1438923806 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2877847613) ^ 4 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_359
      · exact prime_fortyNineAU_677
      · exact prime_fortyNineAU_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3838869493 : Nat.Prime 3838869493 := by
  apply lucas_primality 3838869493 (2 : ZMod 3838869493)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (319905791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (319905791, 1)] : List FactorBlock).map factorBlockValue).prod) = 3838869493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_319905791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3838869493) ^ 1919434746 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3838869493) ^ 1279623164 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3838869493) ^ 12 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3898535677 : Nat.Prime 3898535677 := by
  apply lucas_primality 3898535677 (5 : ZMod 3898535677)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (41, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (41, 1), (66587, 1)] : List FactorBlock).map factorBlockValue).prod) = 3898535677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_66587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3898535677) ^ 1949267838 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3898535677) ^ 1299511892 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3898535677) ^ 556933668 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3898535677) ^ 229325628 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3898535677) ^ 95086236 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3898535677) ^ 58548 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4482657419 : Nat.Prime 4482657419 := by
  apply lucas_primality 4482657419 (2 : ZMod 4482657419)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (751, 1), (40883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (751, 1), (40883, 1)] : List FactorBlock).map factorBlockValue).prod) = 4482657419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_73
      · exact prime_fortyNineAU_751
      · exact prime_fortyNineAU_40883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4482657419) ^ 2241328709 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4482657419) ^ 61406266 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4482657419) ^ 5968918 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4482657419) ^ 109646 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4548928963 : Nat.Prime 4548928963 := by
  apply lucas_primality 4548928963 (3 : ZMod 4548928963)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (71, 1), (191, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (71, 1), (191, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 4548928963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_71
      · exact prime_fortyNineAU_191
      · exact prime_fortyNineAU_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4548928963) ^ 2274464481 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4548928963) ^ 1516309654 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4548928963) ^ 122944026 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4548928963) ^ 64069422 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4548928963) ^ 23816382 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4548928963) ^ 3010542 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4605692251 : Nat.Prime 4605692251 := by
  apply lucas_primality 4605692251 (3 : ZMod 4605692251)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (6140923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (6140923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4605692251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_6140923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4605692251) ^ 2302846125 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4605692251) ^ 1535230750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4605692251) ^ 921138450 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4605692251) ^ 750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_5803704331 : Nat.Prime 5803704331 := by
  apply lucas_primality 5803704331 (15 : ZMod 5803704331)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (499, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (499, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) = 5803704331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_499
      · exact prime_fortyNineAU_6571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 5803704331) ^ 2901852165 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (15 : ZMod 5803704331) ^ 1934568110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (15 : ZMod 5803704331) ^ 1160740866 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (15 : ZMod 5803704331) ^ 98367870 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (15 : ZMod 5803704331) ^ 11630670 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (15 : ZMod 5803704331) ^ 883230 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_5975119841 : Nat.Prime 5975119841 := by
  apply lucas_primality 5975119841 (6 : ZMod 5975119841)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (37344499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (37344499, 1)] : List FactorBlock).map factorBlockValue).prod) = 5975119841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_37344499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5975119841) ^ 2987559920 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975119841) ^ 1195023968 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975119841) ^ 160 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_6958755691 : Nat.Prime 6958755691 := by
  apply lucas_primality 6958755691 (3 : ZMod 6958755691)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (31, 1), (83, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (31, 1), (83, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 6958755691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_83
      · exact prime_fortyNineAU_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6958755691) ^ 3479377845 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 2319585230 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 1391751138 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 409338570 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 224475990 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 83840430 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6958755691) ^ 1312230 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7182811409 : Nat.Prime 7182811409 := by
  apply lucas_primality 7182811409 (3 : ZMod 7182811409)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (15480197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (15480197, 1)] : List FactorBlock).map factorBlockValue).prod) = 7182811409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_15480197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7182811409) ^ 3591405704 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7182811409) ^ 247683152 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7182811409) ^ 464 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7236921331 : Nat.Prime 7236921331 := by
  apply lucas_primality 7236921331 (2 : ZMod 7236921331)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1009, 1), (79693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1009, 1), (79693, 1)] : List FactorBlock).map factorBlockValue).prod) = 7236921331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_1009
      · exact prime_fortyNineAU_79693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7236921331) ^ 3618460665 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236921331) ^ 2412307110 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236921331) ^ 1447384266 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236921331) ^ 7172370 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7236921331) ^ 90810 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7304185061 : Nat.Prime 7304185061 := by
  apply lucas_primality 7304185061 (3 : ZMod 7304185061)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (365209253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (365209253, 1)] : List FactorBlock).map factorBlockValue).prod) = 7304185061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_365209253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7304185061) ^ 3652092530 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7304185061) ^ 1460837012 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7304185061) ^ 20 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7898131057 : Nat.Prime 7898131057 := by
  apply lucas_primality 7898131057 (5 : ZMod 7898131057)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (9649, 1), (17053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (9649, 1), (17053, 1)] : List FactorBlock).map factorBlockValue).prod) = 7898131057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_9649
      · exact prime_fortyNineAU_17053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7898131057) ^ 3949065528 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7898131057) ^ 2632710352 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7898131057) ^ 818544 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7898131057) ^ 463152 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7973718653 : Nat.Prime 7973718653 := by
  apply lucas_primality 7973718653 (2 : ZMod 7973718653)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1993429663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1993429663, 1)] : List FactorBlock).map factorBlockValue).prod) = 7973718653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1993429663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7973718653) ^ 3986859326 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7973718653) ^ 4 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_9750971521 : Nat.Prime 9750971521 := by
  apply lucas_primality 9750971521 (19 : ZMod 9750971521)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (17, 1), (99581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (17, 1), (99581, 1)] : List FactorBlock).map factorBlockValue).prod) = 9750971521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_99581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 9750971521) ^ 4875485760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 9750971521) ^ 3250323840 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 9750971521) ^ 1950194304 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 9750971521) ^ 573586560 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (19 : ZMod 9750971521) ^ 97920 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_9862917541 : Nat.Prime 9862917541 := by
  apply lucas_primality 9862917541 (2 : ZMod 9862917541)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (907, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (907, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 9862917541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_907
      · exact prime_fortyNineAU_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9862917541) ^ 4931458770 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 3287639180 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 1972583508 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 1408988220 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 580171620 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 10874220 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9862917541) ^ 6475980 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_10327330249 : Nat.Prime 10327330249 := by
  apply lucas_primality 10327330249 (13 : ZMod 10327330249)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (229, 1), (599, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (229, 1), (599, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) = 10327330249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_229
      · exact prime_fortyNineAU_599
      · exact prime_fortyNineAU_3137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10327330249) ^ 5163665124 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10327330249) ^ 3442443416 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10327330249) ^ 45097512 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10327330249) ^ 17240952 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 10327330249) ^ 3292104 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_11094972283 : Nat.Prime 11094972283 := by
  apply lucas_primality 11094972283 (2 : ZMod 11094972283)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (373, 1), (1652513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (373, 1), (1652513, 1)] : List FactorBlock).map factorBlockValue).prod) = 11094972283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_373
      · exact prime_fortyNineAU_1652513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11094972283) ^ 5547486141 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11094972283) ^ 3698324094 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11094972283) ^ 29745234 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11094972283) ^ 6714 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_11915285693 : Nat.Prime 11915285693 := by
  apply lucas_primality 11915285693 (2 : ZMod 11915285693)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31723, 1), (93901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31723, 1), (93901, 1)] : List FactorBlock).map factorBlockValue).prod) = 11915285693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_31723
      · exact prime_fortyNineAU_93901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11915285693) ^ 5957642846 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11915285693) ^ 375604 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11915285693) ^ 126892 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_14837336249 : Nat.Prime 14837336249 := by
  apply lucas_primality 14837336249 (3 : ZMod 14837336249)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23, 1), (337, 1), (34183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23, 1), (337, 1), (34183, 1)] : List FactorBlock).map factorBlockValue).prod) = 14837336249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_337
      · exact prime_fortyNineAU_34183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14837336249) ^ 7418668124 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14837336249) ^ 2119619464 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14837336249) ^ 645101576 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14837336249) ^ 44027704 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14837336249) ^ 434056 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_16991844937 : Nat.Prime 16991844937 := by
  apply lucas_primality 16991844937 (5 : ZMod 16991844937)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (64363049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (64363049, 1)] : List FactorBlock).map factorBlockValue).prod) = 16991844937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_64363049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16991844937) ^ 8495922468 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 16991844937) ^ 5663948312 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 16991844937) ^ 1544713176 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 16991844937) ^ 264 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_21494319307 : Nat.Prime 21494319307 := by
  apply lucas_primality 21494319307 (3 : ZMod 21494319307)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (155755937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (155755937, 1)] : List FactorBlock).map factorBlockValue).prod) = 21494319307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_155755937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21494319307) ^ 10747159653 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21494319307) ^ 7164773102 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21494319307) ^ 934535622 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21494319307) ^ 138 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_25464081217 : Nat.Prime 25464081217 := by
  apply lucas_primality 25464081217 (5 : ZMod 25464081217)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (101, 1), (109, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (101, 1), (109, 1), (1721, 1)] : List FactorBlock).map factorBlockValue).prod) = 25464081217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_101
      · exact prime_fortyNineAU_109
      · exact prime_fortyNineAU_1721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25464081217) ^ 12732040608 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25464081217) ^ 8488027072 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25464081217) ^ 3637725888 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25464081217) ^ 252119616 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25464081217) ^ 233615424 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25464081217) ^ 14796096 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_26543086109 : Nat.Prime 26543086109 := by
  apply lucas_primality 26543086109 (2 : ZMod 26543086109)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 2), (19, 1), (412339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 2), (19, 1), (412339, 1)] : List FactorBlock).map factorBlockValue).prod) = 26543086109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_412339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26543086109) ^ 13271543054 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26543086109) ^ 3791869444 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26543086109) ^ 2413007828 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26543086109) ^ 1397004532 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 26543086109) ^ 64372 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_27293573779 : Nat.Prime 27293573779 := by
  apply lucas_primality 27293573779 (2 : ZMod 27293573779)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4548928963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4548928963, 1)] : List FactorBlock).map factorBlockValue).prod) = 27293573779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_4548928963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27293573779) ^ 13646786889 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27293573779) ^ 9097857926 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27293573779) ^ 6 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_30038804161 : Nat.Prime 30038804161 := by
  apply lucas_primality 30038804161 (13 : ZMod 30038804161)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (17, 1), (41, 1), (44893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (17, 1), (41, 1), (44893, 1)] : List FactorBlock).map factorBlockValue).prod) = 30038804161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_44893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 30038804161) ^ 15019402080 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 30038804161) ^ 10012934720 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 30038804161) ^ 6007760832 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 30038804161) ^ 1766988480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 30038804161) ^ 732653760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 30038804161) ^ 669120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_33705602543 : Nat.Prime 33705602543 := by
  apply lucas_primality 33705602543 (5 : ZMod 33705602543)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (104579, 1), (161149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (104579, 1), (161149, 1)] : List FactorBlock).map factorBlockValue).prod) = 33705602543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_104579
      · exact prime_fortyNineAU_161149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33705602543) ^ 16852801271 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33705602543) ^ 322298 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33705602543) ^ 209158 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_36847620883 : Nat.Prime 36847620883 := by
  apply lucas_primality 36847620883 (2 : ZMod 36847620883)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2047090049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2047090049, 1)] : List FactorBlock).map factorBlockValue).prod) = 36847620883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_2047090049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36847620883) ^ 18423810441 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36847620883) ^ 12282540294 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36847620883) ^ 18 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_43263636359 : Nat.Prime 43263636359 := by
  apply lucas_primality 43263636359 (11 : ZMod 43263636359)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (397, 1), (409, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (397, 1), (409, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 43263636359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_127
      · exact prime_fortyNineAU_397
      · exact prime_fortyNineAU_409
      · exact prime_fortyNineAU_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 43263636359) ^ 21631818179 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 43263636359) ^ 340658554 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 43263636359) ^ 108976414 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 43263636359) ^ 105779062 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 43263636359) ^ 41242742 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_45833121487 : Nat.Prime 45833121487 := by
  apply lucas_primality 45833121487 (5 : ZMod 45833121487)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (103, 1), (2746801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (103, 1), (2746801, 1)] : List FactorBlock).map factorBlockValue).prod) = 45833121487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_103
      · exact prime_fortyNineAU_2746801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45833121487) ^ 22916560743 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 45833121487) ^ 15277707162 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 45833121487) ^ 444981762 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 45833121487) ^ 16686 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_46746322157 : Nat.Prime 46746322157 := by
  apply lucas_primality 46746322157 (2 : ZMod 46746322157)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (3709, 1), (101641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (3709, 1), (101641, 1)] : List FactorBlock).map factorBlockValue).prod) = 46746322157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_3709
      · exact prime_fortyNineAU_101641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46746322157) ^ 23373161078 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46746322157) ^ 1507945876 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46746322157) ^ 12603484 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46746322157) ^ 459916 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_53086172219 : Nat.Prime 53086172219 := by
  apply lucas_primality 53086172219 (2 : ZMod 53086172219)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26543086109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26543086109, 1)] : List FactorBlock).map factorBlockValue).prod) = 53086172219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_26543086109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 53086172219) ^ 26543086109 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53086172219) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_70456593989 : Nat.Prime 70456593989 := by
  apply lucas_primality 70456593989 (2 : ZMod 70456593989)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1601286227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1601286227, 1)] : List FactorBlock).map factorBlockValue).prod) = 70456593989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_1601286227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70456593989) ^ 35228296994 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70456593989) ^ 6405144908 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70456593989) ^ 44 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_73
      · exact prime_fortyNineAU_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_81826801477 : Nat.Prime 81826801477 := by
  apply lucas_primality 81826801477 (14 : ZMod 81826801477)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (29, 1), (347, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (29, 1), (347, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) = 81826801477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_347
      · exact prime_fortyNineAU_13829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 81826801477) ^ 40913400738 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 81826801477) ^ 27275600492 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 81826801477) ^ 11689543068 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 81826801477) ^ 2821613844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 81826801477) ^ 235812108 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 81826801477) ^ 5917044 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_90311985749 : Nat.Prime 90311985749 := by
  apply lucas_primality 90311985749 (2 : ZMod 90311985749)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (853, 1), (1150823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (853, 1), (1150823, 1)] : List FactorBlock).map factorBlockValue).prod) = 90311985749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_853
      · exact prime_fortyNineAU_1150823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90311985749) ^ 45155992874 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 90311985749) ^ 3926608076 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 90311985749) ^ 105875716 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 90311985749) ^ 78476 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_109509651193 : Nat.Prime 109509651193 := by
  apply lucas_primality 109509651193 (5 : ZMod 109509651193)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (26449, 1), (172517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (26449, 1), (172517, 1)] : List FactorBlock).map factorBlockValue).prod) = 109509651193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_26449
      · exact prime_fortyNineAU_172517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 109509651193) ^ 54754825596 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 109509651193) ^ 36503217064 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 109509651193) ^ 4140408 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 109509651193) ^ 634776 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_115085611999 : Nat.Prime 115085611999 := by
  apply lucas_primality 115085611999 (3 : ZMod 115085611999)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (653, 1), (466247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (653, 1), (466247, 1)] : List FactorBlock).map factorBlockValue).prod) = 115085611999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_653
      · exact prime_fortyNineAU_466247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115085611999) ^ 57542805999 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 115085611999) ^ 38361870666 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 115085611999) ^ 16440801714 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 115085611999) ^ 176241366 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 115085611999) ^ 246834 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_126639590279 : Nat.Prime 126639590279 := by
  apply lucas_primality 126639590279 (11 : ZMod 126639590279)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28057, 1), (2256827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28057, 1), (2256827, 1)] : List FactorBlock).map factorBlockValue).prod) = 126639590279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_28057
      · exact prime_fortyNineAU_2256827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 126639590279) ^ 63319795139 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 126639590279) ^ 4513654 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 126639590279) ^ 56114 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_146469826597 : Nat.Prime 146469826597 := by
  apply lucas_primality 146469826597 (5 : ZMod 146469826597)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (393736093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (393736093, 1)] : List FactorBlock).map factorBlockValue).prod) = 146469826597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_393736093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 146469826597) ^ 73234913298 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146469826597) ^ 48823275532 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146469826597) ^ 4724833116 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146469826597) ^ 372 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_325885091473 : Nat.Prime 325885091473 := by
  apply lucas_primality 325885091473 (5 : ZMod 325885091473)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (839, 1), (887, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (839, 1), (887, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod) = 325885091473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_839
      · exact prime_fortyNineAU_887
      · exact prime_fortyNineAU_3041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 325885091473) ^ 162942545736 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 325885091473) ^ 108628363824 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 325885091473) ^ 388420848 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 325885091473) ^ 367401456 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 325885091473) ^ 107163792 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_356055796099 : Nat.Prime 356055796099 := by
  apply lucas_primality 356055796099 (2 : ZMod 356055796099)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (19, 1), (61241107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (19, 1), (61241107, 1)] : List FactorBlock).map factorBlockValue).prod) = 356055796099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_61241107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 356055796099) ^ 178027898049 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356055796099) ^ 118685265366 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356055796099) ^ 20944458594 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356055796099) ^ 18739778742 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356055796099) ^ 5814 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_395901701399 : Nat.Prime 395901701399 := by
  apply lucas_primality 395901701399 (7 : ZMod 395901701399)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (20173, 1), (1401809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (20173, 1), (1401809, 1)] : List FactorBlock).map factorBlockValue).prod) = 395901701399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_20173
      · exact prime_fortyNineAU_1401809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 395901701399) ^ 197950850699 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 395901701399) ^ 56557385914 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 395901701399) ^ 19625326 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 395901701399) ^ 282422 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_397
      · exact prime_fortyNineAU_2531
      · exact prime_fortyNineAU_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_495711851953 : Nat.Prime 495711851953 := by
  apply lucas_primality 495711851953 (5 : ZMod 495711851953)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (10327330249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (10327330249, 1)] : List FactorBlock).map factorBlockValue).prod) = 495711851953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_10327330249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 495711851953) ^ 247855925976 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 495711851953) ^ 165237283984 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 495711851953) ^ 48 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_551734058819 : Nat.Prime 551734058819 := by
  apply lucas_primality 551734058819 (2 : ZMod 551734058819)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (349, 1), (673, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (349, 1), (673, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 551734058819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_157
      · exact prime_fortyNineAU_349
      · exact prime_fortyNineAU_673
      · exact prime_fortyNineAU_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 551734058819) ^ 275867029409 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 551734058819) ^ 3514229674 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 551734058819) ^ 1580899882 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 551734058819) ^ 819812866 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 551734058819) ^ 73751378 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_616505944823 : Nat.Prime 616505944823 := by
  apply lucas_primality 616505944823 (5 : ZMod 616505944823)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (67, 1), (691, 1), (154841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (67, 1), (691, 1), (154841, 1)] : List FactorBlock).map factorBlockValue).prod) = 616505944823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_691
      · exact prime_fortyNineAU_154841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 616505944823) ^ 308252972411 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 616505944823) ^ 14337347554 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 616505944823) ^ 9201581266 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 616505944823) ^ 892193842 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 616505944823) ^ 3981542 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_644224421153 : Nat.Prime 644224421153 := by
  apply lucas_primality 644224421153 (3 : ZMod 644224421153)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (19181, 1), (80737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (19181, 1), (80737, 1)] : List FactorBlock).map factorBlockValue).prod) = 644224421153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_19181
      · exact prime_fortyNineAU_80737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 644224421153) ^ 322112210576 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 644224421153) ^ 49555724704 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 644224421153) ^ 33586592 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 644224421153) ^ 7979296 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_655504518509 : Nat.Prime 655504518509 := by
  apply lucas_primality 655504518509 (2 : ZMod 655504518509)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (1377110333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (1377110333, 1)] : List FactorBlock).map factorBlockValue).prod) = 655504518509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_1377110333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 655504518509) ^ 327752259254 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 655504518509) ^ 93643502644 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 655504518509) ^ 38559089324 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 655504518509) ^ 476 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_662130753797 : Nat.Prime 662130753797 := by
  apply lucas_primality 662130753797 (2 : ZMod 662130753797)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239, 1), (692605391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239, 1), (692605391, 1)] : List FactorBlock).map factorBlockValue).prod) = 662130753797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_239
      · exact prime_fortyNineAU_692605391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 662130753797) ^ 331065376898 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 662130753797) ^ 2770421564 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 662130753797) ^ 956 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_834575807771 : Nat.Prime 834575807771 := by
  apply lucas_primality 834575807771 (2 : ZMod 834575807771)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (2877847613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (2877847613, 1)] : List FactorBlock).map factorBlockValue).prod) = 834575807771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_2877847613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 834575807771) ^ 417287903885 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 834575807771) ^ 166915161554 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 834575807771) ^ 28778476130 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 834575807771) ^ 290 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_878818959583 : Nat.Prime 878818959583 := by
  apply lucas_primality 878818959583 (3 : ZMod 878818959583)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (146469826597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (146469826597, 1)] : List FactorBlock).map factorBlockValue).prod) = 878818959583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_146469826597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 878818959583) ^ 439409479791 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 878818959583) ^ 292939653194 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 878818959583) ^ 6 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1406549534531 : Nat.Prime 1406549534531 := by
  apply lucas_primality 1406549534531 (2 : ZMod 1406549534531)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (31, 1), (109, 1), (312979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (31, 1), (109, 1), (312979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406549534531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_109
      · exact prime_fortyNineAU_312979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406549534531) ^ 703274767265 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 281309906906 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 200935647790 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 74028922870 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 45372565630 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 12904124170 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406549534531) ^ 4494070 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1501762763693 : Nat.Prime 1501762763693 := by
  apply lucas_primality 1501762763693 (2 : ZMod 1501762763693)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (2207, 1), (7396243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (2207, 1), (7396243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1501762763693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_2207
      · exact prime_fortyNineAU_7396243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1501762763693) ^ 750881381846 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501762763693) ^ 65294033204 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501762763693) ^ 680454356 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501762763693) ^ 203044 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_35279
      · exact prime_fortyNineAU_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1604039327479 : Nat.Prime 1604039327479 := by
  apply lucas_primality 1604039327479 (3 : ZMod 1604039327479)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1429, 1), (2689, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1429, 1), (2689, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1604039327479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_1429
      · exact prime_fortyNineAU_2689
      · exact prime_fortyNineAU_3313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1604039327479) ^ 802019663739 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604039327479) ^ 534679775826 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604039327479) ^ 229148475354 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604039327479) ^ 1122490782 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604039327479) ^ 596518902 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1604039327479) ^ 484165206 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1857666990079 : Nat.Prime 1857666990079 := by
  apply lucas_primality 1857666990079 (3 : ZMod 1857666990079)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2897, 1), (11874781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2897, 1), (11874781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1857666990079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_2897
      · exact prime_fortyNineAU_11874781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1857666990079) ^ 928833495039 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1857666990079) ^ 619222330026 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1857666990079) ^ 641238174 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1857666990079) ^ 156438 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1985751166879 : Nat.Prime 1985751166879 := by
  apply lucas_primality 1985751166879 (3 : ZMod 1985751166879)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1153, 1), (31893469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1153, 1), (31893469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1985751166879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_1153
      · exact prime_fortyNineAU_31893469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1985751166879) ^ 992875583439 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1985751166879) ^ 661917055626 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1985751166879) ^ 1722247326 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1985751166879) ^ 62262 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2130101955587 : Nat.Prime 2130101955587 := by
  apply lucas_primality 2130101955587 (2 : ZMod 2130101955587)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (89819, 1), (1077977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (89819, 1), (1077977, 1)] : List FactorBlock).map factorBlockValue).prod) = 2130101955587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_89819
      · exact prime_fortyNineAU_1077977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2130101955587) ^ 1065050977793 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2130101955587) ^ 193645632326 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2130101955587) ^ 23715494 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2130101955587) ^ 1976018 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2197277019473 : Nat.Prime 2197277019473 := by
  apply lucas_primality 2197277019473 (3 : ZMod 2197277019473)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4993, 1), (27504469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4993, 1), (27504469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2197277019473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_4993
      · exact prime_fortyNineAU_27504469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2197277019473) ^ 1098638509736 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2197277019473) ^ 440071504 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2197277019473) ^ 79888 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2755349978497 : Nat.Prime 2755349978497 := by
  apply lucas_primality 2755349978497 (11 : ZMod 2755349978497)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (23, 1), (29, 1), (71, 1), (151517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (23, 1), (29, 1), (71, 1), (151517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2755349978497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_71
      · exact prime_fortyNineAU_151517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2755349978497) ^ 1377674989248 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2755349978497) ^ 918449992832 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2755349978497) ^ 119797825152 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2755349978497) ^ 95012068224 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2755349978497) ^ 38807746176 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2755349978497) ^ 18185088 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2813099069063 : Nat.Prime 2813099069063 := by
  apply lucas_primality 2813099069063 (5 : ZMod 2813099069063)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1406549534531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1406549534531, 1)] : List FactorBlock).map factorBlockValue).prod) = 2813099069063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1406549534531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2813099069063) ^ 1406549534531 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2813099069063) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2960464632287 : Nat.Prime 2960464632287 := by
  apply lucas_primality 2960464632287 (5 : ZMod 2960464632287)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (41, 1), (1601, 1), (103919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (41, 1), (1601, 1), (103919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2960464632287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_1601
      · exact prime_fortyNineAU_103919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2960464632287) ^ 1480232316143 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2960464632287) ^ 422923518898 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2960464632287) ^ 95498859106 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2960464632287) ^ 72206454446 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2960464632287) ^ 1849134686 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2960464632287) ^ 28488194 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2975609680819 : Nat.Prime 2975609680819 := by
  apply lucas_primality 2975609680819 (2 : ZMod 2975609680819)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (5975119841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (5975119841, 1)] : List FactorBlock).map factorBlockValue).prod) = 2975609680819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_83
      · exact prime_fortyNineAU_5975119841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2975609680819) ^ 1487804840409 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975609680819) ^ 991869893606 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975609680819) ^ 35850719046 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975609680819) ^ 498 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3300095650451 : Nat.Prime 3300095650451 := by
  apply lucas_primality 3300095650451 (6 : ZMod 3300095650451)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (179, 1), (368725771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (179, 1), (368725771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3300095650451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_179
      · exact prime_fortyNineAU_368725771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3300095650451) ^ 1650047825225 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3300095650451) ^ 660019130090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3300095650451) ^ 18436288550 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3300095650451) ^ 8950 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3315549565847 : Nat.Prime 3315549565847 := by
  apply lucas_primality 3315549565847 (5 : ZMod 3315549565847)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (29, 1), (1166625463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (29, 1), (1166625463, 1)] : List FactorBlock).map factorBlockValue).prod) = 3315549565847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_1166625463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3315549565847) ^ 1657774782923 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3315549565847) ^ 473649937978 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3315549565847) ^ 114329295374 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3315549565847) ^ 2842 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3406593075433 : Nat.Prime 3406593075433 := by
  apply lucas_primality 3406593075433 (5 : ZMod 3406593075433)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (199, 1), (713273257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (199, 1), (713273257, 1)] : List FactorBlock).map factorBlockValue).prod) = 3406593075433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_199
      · exact prime_fortyNineAU_713273257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3406593075433) ^ 1703296537716 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3406593075433) ^ 1135531025144 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3406593075433) ^ 17118558168 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3406593075433) ^ 4776 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3819641174311 : Nat.Prime 3819641174311 := by
  apply lucas_primality 3819641174311 (3 : ZMod 3819641174311)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (8179, 1), (1197451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (8179, 1), (1197451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3819641174311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_8179
      · exact prime_fortyNineAU_1197451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3819641174311) ^ 1909820587155 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3819641174311) ^ 1273213724770 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3819641174311) ^ 763928234862 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3819641174311) ^ 293818551870 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3819641174311) ^ 467005890 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3819641174311) ^ 3189810 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4930463408441 : Nat.Prime 4930463408441 := by
  apply lucas_primality 4930463408441 (3 : ZMod 4930463408441)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (23, 1), (53, 1), (1187, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (23, 1), (53, 1), (1187, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4930463408441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_1187
      · exact prime_fortyNineAU_5011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4930463408441) ^ 2465231704220 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 986092681688 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 290027259320 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 214367974280 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 93027611480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 4153718120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4930463408441) ^ 983928040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_5718246885269 : Nat.Prime 5718246885269 := by
  apply lucas_primality 5718246885269 (2 : ZMod 5718246885269)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (7898131057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (7898131057, 1)] : List FactorBlock).map factorBlockValue).prod) = 5718246885269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_181
      · exact prime_fortyNineAU_7898131057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5718246885269) ^ 2859123442634 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5718246885269) ^ 31592524228 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5718246885269) ^ 724 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7208113129753 : Nat.Prime 7208113129753 := by
  apply lucas_primality 7208113129753 (5 : ZMod 7208113129753)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (4482657419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (4482657419, 1)] : List FactorBlock).map factorBlockValue).prod) = 7208113129753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_4482657419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7208113129753) ^ 3604056564876 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7208113129753) ^ 2402704376584 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7208113129753) ^ 107583778056 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7208113129753) ^ 1608 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_8560197254309 : Nat.Prime 8560197254309 := by
  apply lucas_primality 8560197254309 (2 : ZMod 8560197254309)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (383, 1), (853, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (383, 1), (853, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560197254309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_383
      · exact prime_fortyNineAU_853
      · exact prime_fortyNineAU_13967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560197254309) ^ 4280098627154 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560197254309) ^ 1222885322044 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560197254309) ^ 127764138124 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560197254309) ^ 22350384476 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560197254309) ^ 10035401236 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560197254309) ^ 612887324 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_9360771698401 : Nat.Prime 9360771698401 := by
  apply lucas_primality 9360771698401 (13 : ZMod 9360771698401)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (58031, 1), (67211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (58031, 1), (67211, 1)] : List FactorBlock).map factorBlockValue).prod) = 9360771698401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_58031
      · exact prime_fortyNineAU_67211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9360771698401) ^ 4680385849200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 9360771698401) ^ 3120257232800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 9360771698401) ^ 1872154339680 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 9360771698401) ^ 161306400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (13 : ZMod 9360771698401) ^ 139274400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_10931383994611 : Nat.Prime 10931383994611 := by
  apply lucas_primality 10931383994611 (2 : ZMod 10931383994611)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (112291, 1), (3244957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (112291, 1), (3244957, 1)] : List FactorBlock).map factorBlockValue).prod) = 10931383994611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_112291
      · exact prime_fortyNineAU_3244957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10931383994611) ^ 5465691997305 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931383994611) ^ 3643794664870 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931383994611) ^ 2186276798922 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931383994611) ^ 97348710 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931383994611) ^ 3368730 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_11218404309401 : Nat.Prime 11218404309401 := by
  apply lucas_primality 11218404309401 (6 : ZMod 11218404309401)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (127, 1), (441669461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (127, 1), (441669461, 1)] : List FactorBlock).map factorBlockValue).prod) = 11218404309401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_127
      · exact prime_fortyNineAU_441669461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11218404309401) ^ 5609202154700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11218404309401) ^ 2243680861880 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11218404309401) ^ 88333892200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11218404309401) ^ 25400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_971
      · exact prime_fortyNineAU_1031
      · exact prime_fortyNineAU_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_15151710392213 : Nat.Prime 15151710392213 := by
  apply lucas_primality 15151710392213 (2 : ZMod 15151710392213)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (135929, 1), (753161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (135929, 1), (753161, 1)] : List FactorBlock).map factorBlockValue).prod) = 15151710392213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_135929
      · exact prime_fortyNineAU_753161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15151710392213) ^ 7575855196106 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15151710392213) ^ 409505686276 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15151710392213) ^ 111467828 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15151710392213) ^ 20117492 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_97
      · exact prime_fortyNineAU_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_32189445165421 : Nat.Prime 32189445165421 := by
  apply lucas_primality 32189445165421 (6 : ZMod 32189445165421)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (34543, 1), (5177033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (34543, 1), (5177033, 1)] : List FactorBlock).map factorBlockValue).prod) = 32189445165421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_34543
      · exact prime_fortyNineAU_5177033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32189445165421) ^ 16094722582710 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 32189445165421) ^ 10729815055140 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 32189445165421) ^ 6437889033084 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 32189445165421) ^ 931865940 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 32189445165421) ^ 6217740 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_293
      · exact prime_fortyNineAU_317
      · exact prime_fortyNineAU_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_101
      · exact prime_fortyNineAU_5779
      · exact prime_fortyNineAU_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_601
      · exact prime_fortyNineAU_1069
      · exact prime_fortyNineAU_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_41783665617779 : Nat.Prime 41783665617779 := by
  apply lucas_primality 41783665617779 (2 : ZMod 41783665617779)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (269, 1), (11094972283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (269, 1), (11094972283, 1)] : List FactorBlock).map factorBlockValue).prod) = 41783665617779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_269
      · exact prime_fortyNineAU_11094972283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41783665617779) ^ 20891832808889 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41783665617779) ^ 5969095088254 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41783665617779) ^ 155329611962 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41783665617779) ^ 3766 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_53423642393267 : Nat.Prime 53423642393267 := by
  apply lucas_primality 53423642393267 (2 : ZMod 53423642393267)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1049, 1), (25464081217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1049, 1), (25464081217, 1)] : List FactorBlock).map factorBlockValue).prod) = 53423642393267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1049
      · exact prime_fortyNineAU_25464081217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53423642393267) ^ 26711821196633 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53423642393267) ^ 50928162434 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53423642393267) ^ 2098 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_69218911573381 : Nat.Prime 69218911573381 := by
  apply lucas_primality 69218911573381 (7 : ZMod 69218911573381)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (307, 1), (1252604263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (307, 1), (1252604263, 1)] : List FactorBlock).map factorBlockValue).prod) = 69218911573381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_307
      · exact prime_fortyNineAU_1252604263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69218911573381) ^ 34609455786690 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 69218911573381) ^ 23072970524460 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 69218911573381) ^ 13843782314676 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 69218911573381) ^ 225468767340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 69218911573381) ^ 55260 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_78676486710557 : Nat.Prime 78676486710557 := by
  apply lucas_primality 78676486710557 (2 : ZMod 78676486710557)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (139, 1), (697066367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (139, 1), (697066367, 1)] : List FactorBlock).map factorBlockValue).prod) = 78676486710557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_139
      · exact prime_fortyNineAU_697066367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78676486710557) ^ 39338243355278 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78676486710557) ^ 11239498101508 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78676486710557) ^ 2712982300364 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78676486710557) ^ 566017890004 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78676486710557) ^ 112868 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_98011937938903 : Nat.Prime 98011937938903 := by
  apply lucas_primality 98011937938903 (6 : ZMod 98011937938903)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (37, 1), (127, 1), (163, 1), (1640557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (37, 1), (127, 1), (163, 1), (1640557, 1)] : List FactorBlock).map factorBlockValue).prod) = 98011937938903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_127
      · exact prime_fortyNineAU_163
      · exact prime_fortyNineAU_1640557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98011937938903) ^ 49005968969451 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 32670645979634 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 7539379841454 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 2648971295646 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 771747542826 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 601300232754 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 98011937938903) ^ 59743086 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_182905223553389 : Nat.Prime 182905223553389 := by
  apply lucas_primality 182905223553389 (2 : ZMod 182905223553389)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (283, 1), (50741, 1), (454907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (283, 1), (50741, 1), (454907, 1)] : List FactorBlock).map factorBlockValue).prod) = 182905223553389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_283
      · exact prime_fortyNineAU_50741
      · exact prime_fortyNineAU_454907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 182905223553389) ^ 91452611776694 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 182905223553389) ^ 26129317650484 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 182905223553389) ^ 646308210436 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 182905223553389) ^ 3604683068 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 182905223553389) ^ 402071684 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_212811085471027 : Nat.Prime 212811085471027 := by
  apply lucas_primality 212811085471027 (2 : ZMod 212811085471027)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (89153, 1), (719419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (89153, 1), (719419, 1)] : List FactorBlock).map factorBlockValue).prod) = 212811085471027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_79
      · exact prime_fortyNineAU_89153
      · exact prime_fortyNineAU_719419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212811085471027) ^ 106405542735513 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212811085471027) ^ 70937028490342 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212811085471027) ^ 30401583638718 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212811085471027) ^ 2693811208494 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212811085471027) ^ 2387032242 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 212811085471027) ^ 295809654 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_219845893615097 : Nat.Prime 219845893615097 := by
  apply lucas_primality 219845893615097 (3 : ZMod 219845893615097)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (50383, 1), (11131361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (50383, 1), (11131361, 1)] : List FactorBlock).map factorBlockValue).prod) = 219845893615097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_50383
      · exact prime_fortyNineAU_11131361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 219845893615097) ^ 109922946807548 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 219845893615097) ^ 31406556230728 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 219845893615097) ^ 4363493512 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 219845893615097) ^ 19750136 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_242616773704061 : Nat.Prime 242616773704061 := by
  apply lucas_primality 242616773704061 (2 : ZMod 242616773704061)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (47, 1), (67, 1), (550326121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (47, 1), (67, 1), (550326121, 1)] : List FactorBlock).map factorBlockValue).prod) = 242616773704061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_550326121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 242616773704061) ^ 121308386852030 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 242616773704061) ^ 48523354740812 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 242616773704061) ^ 34659539100580 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 242616773704061) ^ 5162059014980 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 242616773704061) ^ 3621145876180 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 242616773704061) ^ 440860 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_257407460735179 : Nat.Prime 257407460735179 := by
  apply lucas_primality 257407460735179 (2 : ZMod 257407460735179)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3300095650451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3300095650451, 1)] : List FactorBlock).map factorBlockValue).prod) = 257407460735179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_3300095650451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 257407460735179) ^ 128703730367589 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 257407460735179) ^ 85802486911726 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 257407460735179) ^ 19800573902706 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 257407460735179) ^ 78 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_260573871198287 : Nat.Prime 260573871198287 := by
  apply lucas_primality 260573871198287 (5 : ZMod 260573871198287)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (457, 1), (28081, 1), (534341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (457, 1), (28081, 1), (534341, 1)] : List FactorBlock).map factorBlockValue).prod) = 260573871198287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_457
      · exact prime_fortyNineAU_28081
      · exact prime_fortyNineAU_534341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 260573871198287) ^ 130286935599143 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 260573871198287) ^ 13714414273594 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 260573871198287) ^ 570183525598 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 260573871198287) ^ 9279365806 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 260573871198287) ^ 487654646 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_292943780504657 : Nat.Prime 292943780504657 := by
  apply lucas_primality 292943780504657 (3 : ZMod 292943780504657)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2549, 1), (7182811409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2549, 1), (7182811409, 1)] : List FactorBlock).map factorBlockValue).prod) = 292943780504657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_2549
      · exact prime_fortyNineAU_7182811409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 292943780504657) ^ 146471890252328 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 292943780504657) ^ 114924982544 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 292943780504657) ^ 40784 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_332116793722253 : Nat.Prime 332116793722253 := by
  apply lucas_primality 332116793722253 (2 : ZMod 332116793722253)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (149, 1), (7236921331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (149, 1), (7236921331, 1)] : List FactorBlock).map factorBlockValue).prod) = 332116793722253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_149
      · exact prime_fortyNineAU_7236921331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 332116793722253) ^ 166058396861126 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 332116793722253) ^ 47445256246036 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 332116793722253) ^ 30192435792932 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 332116793722253) ^ 2228971769948 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 332116793722253) ^ 45892 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_423881657580769 : Nat.Prime 423881657580769 := by
  apply lucas_primality 423881657580769 (7 : ZMod 423881657580769)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (131, 1), (33705602543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (131, 1), (33705602543, 1)] : List FactorBlock).map factorBlockValue).prod) = 423881657580769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_131
      · exact prime_fortyNineAU_33705602543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 423881657580769) ^ 211940828790384 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 423881657580769) ^ 141293885860256 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 423881657580769) ^ 3235737844128 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 423881657580769) ^ 12576 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_467319221172283 : Nat.Prime 467319221172283 := by
  apply lucas_primality 467319221172283 (2 : ZMod 467319221172283)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (325885091473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (325885091473, 1)] : List FactorBlock).map factorBlockValue).prod) = 467319221172283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_239
      · exact prime_fortyNineAU_325885091473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 467319221172283) ^ 233659610586141 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 467319221172283) ^ 155773073724094 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 467319221172283) ^ 1955310548838 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 467319221172283) ^ 1434 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_468132081499909 : Nat.Prime 468132081499909 := by
  apply lucas_primality 468132081499909 (11 : ZMod 468132081499909)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (1857666990079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (1857666990079, 1)] : List FactorBlock).map factorBlockValue).prod) = 468132081499909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_1857666990079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 468132081499909) ^ 234066040749954 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 468132081499909) ^ 156044027166636 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 468132081499909) ^ 66876011642844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (11 : ZMod 468132081499909) ^ 252 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_107
      · exact prime_fortyNineAU_233
      · exact prime_fortyNineAU_409
      · exact prime_fortyNineAU_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_778701607084099 : Nat.Prime 778701607084099 := by
  apply lucas_primality 778701607084099 (2 : ZMod 778701607084099)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (22567, 1), (71000429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (22567, 1), (71000429, 1)] : List FactorBlock).map factorBlockValue).prod) = 778701607084099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_22567
      · exact prime_fortyNineAU_71000429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 778701607084099) ^ 389350803542049 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 778701607084099) ^ 259567202361366 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 778701607084099) ^ 34506208494 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 778701607084099) ^ 10967562 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_786468672507043 : Nat.Prime 786468672507043 := by
  apply lucas_primality 786468672507043 (5 : ZMod 786468672507043)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2377, 1), (2625921271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2377, 1), (2625921271, 1)] : List FactorBlock).map factorBlockValue).prod) = 786468672507043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_2377
      · exact prime_fortyNineAU_2625921271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 786468672507043) ^ 393234336253521 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 786468672507043) ^ 262156224169014 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 786468672507043) ^ 112352667501006 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 786468672507043) ^ 330866080146 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 786468672507043) ^ 299502 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_223
      · exact prime_fortyNineAU_283
      · exact prime_fortyNineAU_5843
      · exact prime_fortyNineAU_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1306828697477477 : Nat.Prime 1306828697477477 := by
  apply lucas_primality 1306828697477477 (2 : ZMod 1306828697477477)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (40973, 1), (7973718653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (40973, 1), (7973718653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1306828697477477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_40973
      · exact prime_fortyNineAU_7973718653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1306828697477477) ^ 653414348738738 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1306828697477477) ^ 31894874612 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1306828697477477) ^ 163892 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1339035156873989 : Nat.Prime 1339035156873989 := by
  apply lucas_primality 1339035156873989 (2 : ZMod 1339035156873989)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (2813099069063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (2813099069063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1339035156873989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_2813099069063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1339035156873989) ^ 669517578436994 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339035156873989) ^ 191290736696284 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339035156873989) ^ 78766773933764 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1339035156873989) ^ 476 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_5190753062695157 : Nat.Prime 5190753062695157 := by
  apply lucas_primality 5190753062695157 (2 : ZMod 5190753062695157)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (7951, 1), (14837336249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (7951, 1), (14837336249, 1)] : List FactorBlock).map factorBlockValue).prod) = 5190753062695157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_7951
      · exact prime_fortyNineAU_14837336249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5190753062695157) ^ 2595376531347578 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5190753062695157) ^ 471886642063196 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5190753062695157) ^ 652842794956 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5190753062695157) ^ 349844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_9673219319064269 : Nat.Prime 9673219319064269 := by
  apply lucas_primality 9673219319064269 (2 : ZMod 9673219319064269)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (219845893615097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (219845893615097, 1)] : List FactorBlock).map factorBlockValue).prod) = 9673219319064269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_219845893615097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9673219319064269) ^ 4836609659532134 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9673219319064269) ^ 879383574460388 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9673219319064269) ^ 44 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_10173159781938457 : Nat.Prime 10173159781938457 := by
  apply lucas_primality 10173159781938457 (5 : ZMod 10173159781938457)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (423881657580769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (423881657580769, 1)] : List FactorBlock).map factorBlockValue).prod) = 10173159781938457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_423881657580769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10173159781938457) ^ 5086579890969228 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10173159781938457) ^ 3391053260646152 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10173159781938457) ^ 24 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_12420559908216013 : Nat.Prime 12420559908216013 := by
  apply lucas_primality 12420559908216013 (2 : ZMod 12420559908216013)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (29, 1), (5821, 1), (125131961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (29, 1), (5821, 1), (125131961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12420559908216013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_5821
      · exact prime_fortyNineAU_125131961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12420559908216013) ^ 6210279954108006 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420559908216013) ^ 4140186636072004 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420559908216013) ^ 1774365701173716 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420559908216013) ^ 428295169248828 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420559908216013) ^ 2133750198972 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12420559908216013) ^ 99259692 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_13240167880870631 : Nat.Prime 13240167880870631 := by
  apply lucas_primality 13240167880870631 (14 : ZMod 13240167880870631)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (29, 1), (239, 1), (3898535677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (29, 1), (239, 1), (3898535677, 1)] : List FactorBlock).map factorBlockValue).prod) = 13240167880870631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_239
      · exact prime_fortyNineAU_3898535677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13240167880870631) ^ 6620083940435315 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 13240167880870631) ^ 2648033576174126 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 13240167880870631) ^ 1891452554410090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 13240167880870631) ^ 456557513133470 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 13240167880870631) ^ 55398191970170 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 13240167880870631) ^ 3396190 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_14403367008001427 : Nat.Prime 14403367008001427 := by
  apply lucas_primality 14403367008001427 (2 : ZMod 14403367008001427)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (220903, 1), (358253981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (220903, 1), (358253981, 1)] : List FactorBlock).map factorBlockValue).prod) = 14403367008001427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_220903
      · exact prime_fortyNineAU_358253981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14403367008001427) ^ 7201683504000713 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14403367008001427) ^ 2057623858285918 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14403367008001427) ^ 1107951308307802 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14403367008001427) ^ 65202224542 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14403367008001427) ^ 40204346 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_15112986863925893 : Nat.Prime 15112986863925893 := by
  apply lucas_primality 15112986863925893 (2 : ZMod 15112986863925893)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (918563, 1), (132684341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (918563, 1), (132684341, 1)] : List FactorBlock).map factorBlockValue).prod) = 15112986863925893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_918563
      · exact prime_fortyNineAU_132684341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15112986863925893) ^ 7556493431962946 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15112986863925893) ^ 487515705287932 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15112986863925893) ^ 16452858284 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15112986863925893) ^ 113901812 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_25279132400995087 : Nat.Prime 25279132400995087 := by
  apply lucas_primality 25279132400995087 (5 : ZMod 25279132400995087)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (468132081499909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (468132081499909, 1)] : List FactorBlock).map factorBlockValue).prod) = 25279132400995087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_468132081499909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25279132400995087) ^ 12639566200497543 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25279132400995087) ^ 8426377466998362 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 25279132400995087) ^ 54 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_26136573949549541 : Nat.Prime 26136573949549541 := by
  apply lucas_primality 26136573949549541 (3 : ZMod 26136573949549541)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1306828697477477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1306828697477477, 1)] : List FactorBlock).map factorBlockValue).prod) = 26136573949549541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_1306828697477477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26136573949549541) ^ 13068286974774770 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26136573949549541) ^ 5227314789909908 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26136573949549541) ^ 20 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_37858536207159359 : Nat.Prime 37858536207159359 := by
  apply lucas_primality 37858536207159359 (17 : ZMod 37858536207159359)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11801, 1), (1604039327479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11801, 1), (1604039327479, 1)] : List FactorBlock).map factorBlockValue).prod) = 37858536207159359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11801
      · exact prime_fortyNineAU_1604039327479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 37858536207159359) ^ 18929268103579679 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (17 : ZMod 37858536207159359) ^ 3208078654958 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (17 : ZMod 37858536207159359) ^ 23602 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_48520927487394157 : Nat.Prime 48520927487394157 := by
  apply lucas_primality 48520927487394157 (2 : ZMod 48520927487394157)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (212811085471027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (212811085471027, 1)] : List FactorBlock).map factorBlockValue).prod) = 48520927487394157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_212811085471027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48520927487394157) ^ 24260463743697078 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48520927487394157) ^ 16173642495798052 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48520927487394157) ^ 2553733025652324 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48520927487394157) ^ 228 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_49186534555031551 : Nat.Prime 49186534555031551 := by
  apply lucas_primality 49186534555031551 (3 : ZMod 49186534555031551)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (509, 1), (644224421153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (509, 1), (644224421153, 1)] : List FactorBlock).map factorBlockValue).prod) = 49186534555031551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_509
      · exact prime_fortyNineAU_644224421153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49186534555031551) ^ 24593267277515775 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49186534555031551) ^ 16395511518343850 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49186534555031551) ^ 9837306911006310 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49186534555031551) ^ 96633663172950 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 49186534555031551) ^ 76350 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_50137440096763273 : Nat.Prime 50137440096763273 := by
  apply lucas_primality 50137440096763273 (5 : ZMod 50137440096763273)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (4353499, 1), (43623427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (4353499, 1), (43623427, 1)] : List FactorBlock).map factorBlockValue).prod) = 50137440096763273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_4353499
      · exact prime_fortyNineAU_43623427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50137440096763273) ^ 25068720048381636 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 50137440096763273) ^ 16712480032254424 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 50137440096763273) ^ 4557949099705752 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 50137440096763273) ^ 11516584728 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 50137440096763273) ^ 1149323736 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_51768709983971419 : Nat.Prime 51768709983971419 := by
  apply lucas_primality 51768709983971419 (2 : ZMod 51768709983971419)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (2767657, 1), (37560013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (2767657, 1), (37560013, 1)] : List FactorBlock).map factorBlockValue).prod) = 51768709983971419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_83
      · exact prime_fortyNineAU_2767657
      · exact prime_fortyNineAU_37560013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51768709983971419) ^ 25884354991985709 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51768709983971419) ^ 17256236661323806 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51768709983971419) ^ 623719397397246 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51768709983971419) ^ 18704886474 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51768709983971419) ^ 1378293186 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_146326921850365703 : Nat.Prime 146326921850365703 := by
  apply lucas_primality 146326921850365703 (5 : ZMod 146326921850365703)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1171, 1), (72497, 1), (861821473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1171, 1), (72497, 1), (861821473, 1)] : List FactorBlock).map factorBlockValue).prod) = 146326921850365703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_1171
      · exact prime_fortyNineAU_72497
      · exact prime_fortyNineAU_861821473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 146326921850365703) ^ 73163460925182851 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146326921850365703) ^ 124958942656162 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146326921850365703) ^ 2018385889766 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 146326921850365703) ^ 169787974 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_79
      · exact prime_fortyNineAU_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_211594332736121513 : Nat.Prime 211594332736121513 := by
  apply lucas_primality 211594332736121513 (3 : ZMod 211594332736121513)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (108084101, 1), (244710289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (108084101, 1), (244710289, 1)] : List FactorBlock).map factorBlockValue).prod) = 211594332736121513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_108084101
      · exact prime_fortyNineAU_244710289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 211594332736121513) ^ 105797166368060756 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 211594332736121513) ^ 1957682312 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 211594332736121513) ^ 864672808 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_211997554864160267 : Nat.Prime 211997554864160267 := by
  apply lucas_primality 211997554864160267 (2 : ZMod 211997554864160267)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1789, 1), (659539, 1), (2897933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1789, 1), (659539, 1), (2897933, 1)] : List FactorBlock).map factorBlockValue).prod) = 211997554864160267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_1789
      · exact prime_fortyNineAU_659539
      · exact prime_fortyNineAU_2897933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211997554864160267) ^ 105998777432080133 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 211997554864160267) ^ 6838630802069686 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 211997554864160267) ^ 118500589638994 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 211997554864160267) ^ 321432932494 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 211997554864160267) ^ 73154746802 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_61717
      · exact prime_fortyNineAU_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_735667399951481989 : Nat.Prime 735667399951481989 := by
  apply lucas_primality 735667399951481989 (2 : ZMod 735667399951481989)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (401, 1), (81409, 1), (625982537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (401, 1), (81409, 1), (625982537, 1)] : List FactorBlock).map factorBlockValue).prod) = 735667399951481989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_401
      · exact prime_fortyNineAU_81409
      · exact prime_fortyNineAU_625982537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 735667399951481989) ^ 367833699975740994 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 735667399951481989) ^ 245222466650493996 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 735667399951481989) ^ 1834582044766788 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 735667399951481989) ^ 9036683904132 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 735667399951481989) ^ 1175220324 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_870161943018760421 : Nat.Prime 870161943018760421 := by
  apply lucas_primality 870161943018760421 (3 : ZMod 870161943018760421)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (79, 1), (78676486710557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (79, 1), (78676486710557, 1)] : List FactorBlock).map factorBlockValue).prod) = 870161943018760421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_79
      · exact prime_fortyNineAU_78676486710557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 870161943018760421) ^ 435080971509380210 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 870161943018760421) ^ 174032388603752084 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 870161943018760421) ^ 124308849002680060 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 870161943018760421) ^ 11014708139477980 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 870161943018760421) ^ 11060 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_880218536907813487 : Nat.Prime 880218536907813487 := by
  apply lucas_primality 880218536907813487 (5 : ZMod 880218536907813487)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (563, 1), (260573871198287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (563, 1), (260573871198287, 1)] : List FactorBlock).map factorBlockValue).prod) = 880218536907813487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_563
      · exact prime_fortyNineAU_260573871198287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 880218536907813487) ^ 440109268453906743 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 880218536907813487) ^ 293406178969271162 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 880218536907813487) ^ 1563443227189722 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 880218536907813487) ^ 3378 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1192809016904133617 : Nat.Prime 1192809016904133617 := by
  apply lucas_primality 1192809016904133617 (3 : ZMod 1192809016904133617)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 1), (2957, 1), (29741, 1), (3835763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 1), (2957, 1), (29741, 1), (3835763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1192809016904133617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_2957
      · exact prime_fortyNineAU_29741
      · exact prime_fortyNineAU_3835763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1192809016904133617) ^ 596404508452066808 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192809016904133617) ^ 91754539761856432 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192809016904133617) ^ 70165236288478448 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192809016904133617) ^ 403384855226288 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192809016904133617) ^ 40106553811376 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1192809016904133617) ^ 310970468432 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1654660483466783251 : Nat.Prime 1654660483466783251 := by
  apply lucas_primality 1654660483466783251 (3 : ZMod 1654660483466783251)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (31, 1), (1423, 1), (206527, 1), (242161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (31, 1), (1423, 1), (206527, 1), (242161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654660483466783251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_1423
      · exact prime_fortyNineAU_206527
      · exact prime_fortyNineAU_242161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1654660483466783251) ^ 827330241733391625 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 551553494488927750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 330932096693356650 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 53376144627960750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 1162797247692750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 8011836144750 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654660483466783251) ^ 6832894163250 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2315075865962040023 : Nat.Prime 2315075865962040023 := by
  apply lucas_primality 2315075865962040023 (5 : ZMod 2315075865962040023)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (5190753062695157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (5190753062695157, 1)] : List FactorBlock).map factorBlockValue).prod) = 2315075865962040023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_223
      · exact prime_fortyNineAU_5190753062695157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2315075865962040023) ^ 1157537932981020011 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2315075865962040023) ^ 10381506125390314 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2315075865962040023) ^ 446 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3740177464999285811 : Nat.Prime 3740177464999285811 := by
  apply lucas_primality 3740177464999285811 (2 : ZMod 3740177464999285811)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (109, 1), (13327, 1), (6958755691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (109, 1), (13327, 1), (6958755691, 1)] : List FactorBlock).map factorBlockValue).prod) = 3740177464999285811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_109
      · exact prime_fortyNineAU_13327
      · exact prime_fortyNineAU_6958755691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3740177464999285811) ^ 1870088732499642905 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3740177464999285811) ^ 748035492999857162 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3740177464999285811) ^ 101085877432413130 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3740177464999285811) ^ 34313554724764090 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3740177464999285811) ^ 280646617018030 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3740177464999285811) ^ 537477910 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4658716739810258701 : Nat.Prime 4658716739810258701 := by
  apply lucas_primality 4658716739810258701 (6 : ZMod 4658716739810258701)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (37, 1), (1471, 1), (2081, 1), (137106667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (37, 1), (1471, 1), (2081, 1), (137106667, 1)] : List FactorBlock).map factorBlockValue).prod) = 4658716739810258701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_1471
      · exact prime_fortyNineAU_2081
      · exact prime_fortyNineAU_137106667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4658716739810258701) ^ 2329358369905129350 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 1552905579936752900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 931743347962051740 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 125911263238115100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 3167040611699700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 2238691369442700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 4658716739810258701) ^ 33978776100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_7415240457519017869 : Nat.Prime 7415240457519017869 := by
  apply lucas_primality 7415240457519017869 (6 : ZMod 7415240457519017869)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (1473763, 1), (9750971521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (1473763, 1), (9750971521, 1)] : List FactorBlock).map factorBlockValue).prod) = 7415240457519017869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_1473763
      · exact prime_fortyNineAU_9750971521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7415240457519017869) ^ 3707620228759508934 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 7415240457519017869) ^ 2471746819173005956 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 7415240457519017869) ^ 172447452500442276 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 7415240457519017869) ^ 5031501304836 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (6 : ZMod 7415240457519017869) ^ 760461708 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_10051918134028374757 : Nat.Prime 10051918134028374757 := by
  apply lucas_primality 10051918134028374757 (2 : ZMod 10051918134028374757)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (44711, 1), (56737, 1), (330207509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (44711, 1), (56737, 1), (330207509, 1)] : List FactorBlock).map factorBlockValue).prod) = 10051918134028374757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_44711
      · exact prime_fortyNineAU_56737
      · exact prime_fortyNineAU_330207509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10051918134028374757) ^ 5025959067014187378 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051918134028374757) ^ 3350639378009458252 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051918134028374757) ^ 224819801257596 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051918134028374757) ^ 177166895218788 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10051918134028374757) ^ 30441216084 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_12075033107354015473 : Nat.Prime 12075033107354015473 := by
  apply lucas_primality 12075033107354015473 (5 : ZMod 12075033107354015473)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (13240167880870631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (13240167880870631, 1)] : List FactorBlock).map factorBlockValue).prod) = 12075033107354015473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_13240167880870631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12075033107354015473) ^ 6037516553677007736 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12075033107354015473) ^ 4025011035784671824 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12075033107354015473) ^ 635528058281790288 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12075033107354015473) ^ 912 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_75221221193696524753 : Nat.Prime 75221221193696524753 := by
  apply lucas_primality 75221221193696524753 (5 : ZMod 75221221193696524753)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (23, 1), (31, 1), (299059, 1), (188446523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (23, 1), (31, 1), (299059, 1), (188446523, 1)] : List FactorBlock).map factorBlockValue).prod) = 75221221193696524753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_299059
      · exact prime_fortyNineAU_188446523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 75221221193696524753) ^ 37610610596848262376 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 25073740397898841584 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 5786247784130501904 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 3270487877986805424 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 2426491006248274992 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 251526358322928 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 75221221193696524753) ^ 399164813424 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_139
      · exact prime_fortyNineAU_413869
      · exact prime_fortyNineAU_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_278032874282885615741 : Nat.Prime 278032874282885615741 := by
  apply lucas_primality 278032874282885615741 (3 : ZMod 278032874282885615741)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (19, 1), (68422259, 1), (138875111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (19, 1), (68422259, 1), (138875111, 1)] : List FactorBlock).map factorBlockValue).prod) = 278032874282885615741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_68422259
      · exact prime_fortyNineAU_138875111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 278032874282885615741) ^ 139016437141442807870 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 55606574856577123148 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 39718982040412230820 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 25275715843898692340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 14633309172783453460 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 4063485747860 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 278032874282885615741) ^ 2002035298340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_345051237226243542653 : Nat.Prime 345051237226243542653 := by
  apply lucas_primality 345051237226243542653 (2 : ZMod 345051237226243542653)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3617473, 1), (3406593075433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3617473, 1), (3406593075433, 1)] : List FactorBlock).map factorBlockValue).prod) = 345051237226243542653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_3617473
      · exact prime_fortyNineAU_3406593075433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 345051237226243542653) ^ 172525618613121771326 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 345051237226243542653) ^ 49293033889463363236 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 345051237226243542653) ^ 95384606112124 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 345051237226243542653) ^ 101289244 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_775196793635843554093 : Nat.Prime 775196793635843554093 := by
  apply lucas_primality 775196793635843554093 (2 : ZMod 775196793635843554093)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (17, 1), (8460433, 1), (3838869493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (17, 1), (8460433, 1), (3838869493, 1)] : List FactorBlock).map factorBlockValue).prod) = 775196793635843554093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_8460433
      · exact prime_fortyNineAU_3838869493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 775196793635843554093) ^ 387598396817921777046 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 775196793635843554093) ^ 258398931211947851364 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 775196793635843554093) ^ 59630522587372581084 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 775196793635843554093) ^ 45599811390343738476 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 775196793635843554093) ^ 91626137058924 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 775196793635843554093) ^ 201933614844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1884864950003147601119 : Nat.Prime 1884864950003147601119 := by
  apply lucas_primality 1884864950003147601119 (7 : ZMod 1884864950003147601119)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (5503, 1), (1854233, 1), (269272687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (5503, 1), (1854233, 1), (269272687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1884864950003147601119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_5503
      · exact prime_fortyNineAU_1854233
      · exact prime_fortyNineAU_269272687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1884864950003147601119) ^ 942432475001573800559 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1884864950003147601119) ^ 269266421429021085874 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1884864950003147601119) ^ 342515891332572706 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1884864950003147601119) ^ 1016520011240846 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1884864950003147601119) ^ 6999837120514 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2235324097678346398259 : Nat.Prime 2235324097678346398259 := by
  apply lucas_primality 2235324097678346398259 (2 : ZMod 2235324097678346398259)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (937, 1), (1192809016904133617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (937, 1), (1192809016904133617, 1)] : List FactorBlock).map factorBlockValue).prod) = 2235324097678346398259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_937
      · exact prime_fortyNineAU_1192809016904133617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2235324097678346398259) ^ 1117662048839173199129 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2235324097678346398259) ^ 2385618033808267234 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2235324097678346398259) ^ 1874 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_107
      · exact prime_fortyNineAU_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_431
      · exact prime_fortyNineAU_3532679
      · exact prime_fortyNineAU_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_67
      · exact prime_fortyNineAU_19379
      · exact prime_fortyNineAU_311677
      · exact prime_fortyNineAU_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_15398114070722169843929 : Nat.Prime 15398114070722169843929 := by
  apply lucas_primality 15398114070722169843929 (3 : ZMod 15398114070722169843929)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (229, 1), (15233941, 1), (551734058819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (229, 1), (15233941, 1), (551734058819, 1)] : List FactorBlock).map factorBlockValue).prod) = 15398114070722169843929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_229
      · exact prime_fortyNineAU_15233941
      · exact prime_fortyNineAU_551734058819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15398114070722169843929) ^ 7699057035361084921964 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15398114070722169843929) ^ 67240672797913405432 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15398114070722169843929) ^ 1010776795756408 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15398114070722169843929) ^ 27908579912 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_6475879
      · exact prime_fortyNineAU_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1639620664582766079136667 : Nat.Prime 1639620664582766079136667 := by
  apply lucas_primality 1639620664582766079136667 (2 : ZMod 1639620664582766079136667)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (811457, 1), (102433609, 1), (9862917541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (811457, 1), (102433609, 1), (9862917541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1639620664582766079136667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_811457
      · exact prime_fortyNineAU_102433609
      · exact prime_fortyNineAU_9862917541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1639620664582766079136667) ^ 819810332291383039568333 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639620664582766079136667) ^ 2020588477988070938 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639620664582766079136667) ^ 16006666958134474 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639620664582766079136667) ^ 166240938116626 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1819214838620722619898779 : Nat.Prime 1819214838620722619898779 := by
  apply lucas_primality 1819214838620722619898779 (2 : ZMod 1819214838620722619898779)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (22109, 1), (3740177464999285811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (22109, 1), (3740177464999285811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1819214838620722619898779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_22109
      · exact prime_fortyNineAU_3740177464999285811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1819214838620722619898779) ^ 909607419310361309949389 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819214838620722619898779) ^ 165383167147338419990798 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819214838620722619898779) ^ 82283904229984287842 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819214838620722619898779) ^ 486398 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3249625698156632698045477 : Nat.Prime 3249625698156632698045477 := by
  apply lucas_primality 3249625698156632698045477 (2 : ZMod 3249625698156632698045477)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (29, 1), (16749767, 1), (10931383994611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (29, 1), (16749767, 1), (10931383994611, 1)] : List FactorBlock).map factorBlockValue).prod) = 3249625698156632698045477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_16749767
      · exact prime_fortyNineAU_10931383994611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3249625698156632698045477) ^ 1624812849078316349022738 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3249625698156632698045477) ^ 1083208566052210899348492 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3249625698156632698045477) ^ 191154452832743099885028 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3249625698156632698045477) ^ 112056058557125265449844 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3249625698156632698045477) ^ 194010203136356028 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3249625698156632698045477) ^ 297274864716 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3723076948652846472240149 : Nat.Prime 3723076948652846472240149 := by
  apply lucas_primality 3723076948652846472240149 (2 : ZMod 3723076948652846472240149)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19182841, 1), (48520927487394157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19182841, 1), (48520927487394157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3723076948652846472240149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_19182841
      · exact prime_fortyNineAU_48520927487394157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3723076948652846472240149) ^ 1861538474326423236120074 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3723076948652846472240149) ^ 194083709949576628 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3723076948652846472240149) ^ 76731364 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_239
      · exact prime_fortyNineAU_4519
      · exact prime_fortyNineAU_15661
      · exact prime_fortyNineAU_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_6152408381588603558629643 : Nat.Prime 6152408381588603558629643 := by
  apply lucas_primality 6152408381588603558629643 (2 : ZMod 6152408381588603558629643)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (631, 1), (5051, 1), (6669709, 1), (2730396233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (631, 1), (5051, 1), (6669709, 1), (2730396233, 1)] : List FactorBlock).map factorBlockValue).prod) = 6152408381588603558629643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_631
      · exact prime_fortyNineAU_5051
      · exact prime_fortyNineAU_6669709
      · exact prime_fortyNineAU_2730396233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6152408381588603558629643) ^ 3076204190794301779314821 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6152408381588603558629643) ^ 116083177011105727521314 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6152408381588603558629643) ^ 9750251000932810710982 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6152408381588603558629643) ^ 1218057489920531292542 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6152408381588603558629643) ^ 922440301606652338 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6152408381588603558629643) ^ 2253302398834874 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_10686418985618574268226659 : Nat.Prime 10686418985618574268226659 := by
  apply lucas_primality 10686418985618574268226659 (2 : ZMod 10686418985618574268226659)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2309, 1), (42643, 1), (786468672507043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2309, 1), (42643, 1), (786468672507043, 1)] : List FactorBlock).map factorBlockValue).prod) = 10686418985618574268226659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_2309
      · exact prime_fortyNineAU_42643
      · exact prime_fortyNineAU_786468672507043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10686418985618574268226659) ^ 5343209492809287134113329 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10686418985618574268226659) ^ 3562139661872858089408886 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10686418985618574268226659) ^ 464626912418198881227246 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10686418985618574268226659) ^ 4628158937037061181562 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10686418985618574268226659) ^ 250601950744989195606 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10686418985618574268226659) ^ 13587850806 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_1173959
      · exact prime_fortyNineAU_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_991
      · exact prime_fortyNineAU_3779417
      · exact prime_fortyNineAU_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_252974136773092974270990037 : Nat.Prime 252974136773092974270990037 := by
  apply lucas_primality 252974136773092974270990037 (2 : ZMod 252974136773092974270990037)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (148859, 1), (3285647, 1), (3315549565847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (148859, 1), (3285647, 1), (3315549565847, 1)] : List FactorBlock).map factorBlockValue).prod) = 252974136773092974270990037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_148859
      · exact prime_fortyNineAU_3285647
      · exact prime_fortyNineAU_3315549565847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252974136773092974270990037) ^ 126487068386546487135495018 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252974136773092974270990037) ^ 84324712257697658090330012 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252974136773092974270990037) ^ 19459548982545613405460772 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252974136773092974270990037) ^ 1699421175562733689404 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252974136773092974270990037) ^ 76993705280297297388 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252974136773092974270990037) ^ 76299307776588 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_452586541570611649281693113 : Nat.Prime 452586541570611649281693113 := by
  apply lucas_primality 452586541570611649281693113 (3 : ZMod 452586541570611649281693113)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43609, 1), (743573, 1), (38303933, 1), (45547919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43609, 1), (743573, 1), (38303933, 1), (45547919, 1)] : List FactorBlock).map factorBlockValue).prod) = 452586541570611649281693113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_43609
      · exact prime_fortyNineAU_743573
      · exact prime_fortyNineAU_38303933
      · exact prime_fortyNineAU_45547919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 452586541570611649281693113) ^ 226293270785305824640846556 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 452586541570611649281693113) ^ 10378282959265556405368 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 452586541570611649281693113) ^ 608664571697212848344 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 452586541570611649281693113) ^ 11815667638375715864 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (3 : ZMod 452586541570611649281693113) ^ 9936492193432847048 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_585162397182204960687441601 : Nat.Prime 585162397182204960687441601 := by
  apply lucas_primality 585162397182204960687441601 (97 : ZMod 585162397182204960687441601)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 585162397182204960687441601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 585162397182204960687441601) ^ 292581198591102480343720800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 195054132394068320229147200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 117032479436440992137488320 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 83594628168886422955348800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 45012492090938843129803200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 34421317481306174158084800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 30798020904326576878286400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 25441843355748041769019200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 20178013695938102092670400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 18876206360716289054433600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 15815199923843377315876800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 14272253589809877089937600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 13608427841446626992731200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 12450263769834148099732800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 11040799946834055862027200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 9918006731901778994702400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (97 : ZMod 585162397182204960687441601) ^ 9592826183314835421105600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_616288056606790330936773601 : Nat.Prime 616288056606790330936773601 := by
  apply lucas_primality 616288056606790330936773601 (71 : ZMod 616288056606790330936773601)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 616288056606790330936773601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 616288056606790330936773601) ^ 308144028303395165468386800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 205429352202263443645591200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 123257611321358066187354720 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 88041150943827190133824800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 56026186964253666448797600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 47406773585137717764367200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 36252238623928842996280800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 32436213505620543733514400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 26795132895947405692903200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 21251312296785873480578400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 19880259890541623578605600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 16656433962345684619912800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 15031416014799764169189600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 14332280386204426300855200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 11628076539750760961071200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 10445560281471022558250400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (71 : ZMod 616288056606790330936773601) ^ 10103082895193284113717600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_665874451965957369058123201 : Nat.Prime 665874451965957369058123201 := by
  apply lucas_primality 665874451965957369058123201 (87 : ZMod 665874451965957369058123201)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 665874451965957369058123201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (87 : ZMod 665874451965957369058123201) ^ 332937225982978684529061600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 221958150655319123019374400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 133174890393191473811624640 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 95124921709422481294017600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 60534041087814306278011200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 51221111689689028389086400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 39169085409762198179889600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 35046023787681966792532800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 28951063128954668219918400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 21479821031159915130907200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 17996606809890739704273600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 16240840291852618757515200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 15485452371301334164142400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 14167541531190582320385600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 12563668905018063567134400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 11286007660439955407764800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (87 : ZMod 665874451965957369058123201) ^ 10915974622392743755051200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_724138466512978638850708981 : Nat.Prime 724138466512978638850708981 := by
  apply lucas_primality 724138466512978638850708981 (2 : ZMod 724138466512978638850708981)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 724138466512978638850708981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 724138466512978638850708981) ^ 362069233256489319425354490 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 241379488837659546283569660 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 144827693302595727770141796 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 103448352358996948407244140 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 65830769682998058077337180 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 55702958962536818373131460 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 42596380383116390520629940 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 38112550869104138886879420 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 31484281152738201689161260 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 24970291948723401339679620 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 23359305371386407704861580 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 19571309905756179428397540 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 17661913817389722898797780 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 16840429453790200903504860 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 15407201415169758273419340 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 13662989934207144129258660 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 12273533330728451505944220 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (2 : ZMod 724138466512978638850708981) ^ 11871122401852108833618180 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_839580830739685378377633601 : Nat.Prime 839580830739685378377633601 := by
  apply lucas_primality 839580830739685378377633601 (23 : ZMod 839580830739685378377633601)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 839580830739685378377633601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 839580830739685378377633601) ^ 419790415369842689188816800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 279860276913228459459211200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 167916166147937075675526720 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 119940118677097911196804800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 76325530067244125307057600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 64583140826129644490587200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 49387107690569728139860800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 44188464775772914651454400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 28951063128954668219918400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 27083252604505979947665600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 22691373803775280496692800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 20477581237553301911649600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 19525135598597334380875200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 17863421930631603795268800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 15841147749805384497691200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 14230183571859074209790400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (23 : ZMod 839580830739685378377633601) ^ 13763620176060416038977600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 919540909857750652508836801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1053292314927968929237394881 : Nat.Prime 1053292314927968929237394881 := by
  apply lucas_primality 1053292314927968929237394881 (101 : ZMod 1053292314927968929237394881)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1053292314927968929237394881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1053292314927968929237394881) ^ 526646157463984464618697440 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 351097438309322976412464960 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 210658462985593785847478976 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 150470330703995561319627840 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 81022485763689917633645760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 61958371466351113484552640 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 55436437627787838380915520 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 45795318040346475184234560 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 36320424652688583766806720 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 33977171449289320297980480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 28467359862918079168578240 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 25690056461657778761887680 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 24495170114603928586916160 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 22410474785701466579519040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 19873439904301300551648960 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 17852412117423202190464320 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 1053292314927968929237394881) ^ 17267087129966703757990080 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1206897444188297731417848301 : Nat.Prime 1206897444188297731417848301 := by
  apply lucas_primality 1206897444188297731417848301 (14 : ZMod 1206897444188297731417848301)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1206897444188297731417848301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1206897444188297731417848301) ^ 603448722094148865708924150 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 402299148062765910472616100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 241379488837659546283569660 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 172413920598328247345406900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 109717949471663430128895300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 92838264937561363955219100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 70993967305193984201049900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 63520918115173564811465700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 52473801921230336148602100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 41617153247872335566132700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 38932175618977346174769300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 32618849842926965713995900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 29436523028982871497996300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 28067382422983668172508100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 25678669025282930455698900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 22771649890345240215431100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 20455888884547419176573700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (14 : ZMod 1206897444188297731417848301) ^ 19785204003086848056030300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1347234356303216072280388801 : Nat.Prime 1347234356303216072280388801 := by
  apply lucas_primality 1347234356303216072280388801 (79 : ZMod 1347234356303216072280388801)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347234356303216072280388801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1347234356303216072280388801) ^ 673617178151608036140194400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 449078118767738690760129600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 269446871260643214456077760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 192462050900459438897198400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 122475850573019642934580800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 103633412023324313252337600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 79249079782542121898846400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 70907071384379793277915200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 58575406795792003142625600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 46456357113904002492427200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 43459172783974712009044800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 36411739359546380331902400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 32859374543980879811716800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 28664560772408852601710400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 25419516156664454193969600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 22834480615308746987803200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1347234356303216072280388801) ^ 22085809119724853643940800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1609196592251063641890464401 : Nat.Prime 1609196592251063641890464401 := by
  apply lucas_primality 1609196592251063641890464401 (79 : ZMod 1609196592251063641890464401)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1609196592251063641890464401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1609196592251063641890464401) ^ 804598296125531820945232200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 536398864083687880630154800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 321839318450212728378092880 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 229885227464437663127209200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 146290599295551240171860400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 123784353250081818606958800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 94658623073591978934733200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 84694557486898086415287600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 69965069228307114864802800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 55489537663829780754843600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 51909567491969794899692400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 43491799790569287618661200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 39248697371977161997328400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 37423176563978224230010800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 34238225367043907274265200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 30362199853793653620574800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 27274518512729892235431600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1609196592251063641890464401) ^ 26380272004115797408040400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1868744429710912616388926401 : Nat.Prime 1868744429710912616388926401 := by
  apply lucas_primality 1868744429710912616388926401 (79 : ZMod 1868744429710912616388926401)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1868744429710912616388926401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1868744429710912616388926401) ^ 934372214855456308194463200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 622914809903637538796308800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 373748885942182523277785280 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 266963489958701802341275200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 169885857246446601489902400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 143749571516224047414532800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 109926142924171330375819200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 98354969984784874546785600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 81249757813517939842996800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 64439463093479745392721600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 50506606208403043686187200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 45579132431973478448510400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 43459172783974712009044800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 39760519781083247157211200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 35259328862470049365828800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 31673634401879874854049600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1868744429710912616388926401) ^ 30635154585424796989982400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_1931035910701276370268557281 : Nat.Prime 1931035910701276370268557281 := by
  apply lucas_primality 1931035910701276370268557281 (79 : ZMod 1931035910701276370268557281)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931035910701276370268557281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 1931035910701276370268557281) ^ 965517955350638185134278640 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 643678636900425456756185760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 386207182140255274053711456 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 275862272957325195752651040 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 175548719154661488206232480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 148541223900098182328350560 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 113590347688310374721679840 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 101633468984277703698345120 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 83958083073968537837763360 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 66587445196595736905812320 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 62291480990363753879630880 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 52190159748683145142393440 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 47098436846372594396794080 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 44907811876773869076012960 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 41085870440452688729118240 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 36434639824552384344689760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 32729422215275870682517920 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (79 : ZMod 1931035910701276370268557281) ^ 31656326404938956889648480 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_2633230787319922323093487201 : Nat.Prime 2633230787319922323093487201 := by
  apply lucas_primality 2633230787319922323093487201 (55 : ZMod 2633230787319922323093487201)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 4), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2633230787319922323093487201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (55 : ZMod 2633230787319922323093487201) ^ 1316615393659961161546743600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 877743595773307441031162400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 526646157463984464618697440 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 376175826759988903299069600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 202556214409224794084114400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 154895928665877783711381600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 138591094069469595952288800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 114488295100866187960586400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 90801061631721459417016800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 84942928623223300744951200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 71168399657295197921445600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 64225141154144446904719200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 61237925286509821467290400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 56026186964253666448797600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 49683599760753251379122400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 44631030293558005476160800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (55 : ZMod 2633230787319922323093487201) ^ 43167717824916759394975200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3218393184502127283780928801 : Nat.Prime 3218393184502127283780928801 := by
  apply lucas_primality 3218393184502127283780928801 (101 : ZMod 3218393184502127283780928801)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3218393184502127283780928801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 3218393184502127283780928801) ^ 1609196592251063641890464400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 1072797728167375761260309600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 643678636900425456756185760 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 459770454928875326254418400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 292581198591102480343720800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 247568706500163637213917600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 189317246147183957869466400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 169389114973796172830575200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 139930138456614229729605600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 110979075327659561509687200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 103819134983939589799384800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 86983599581138575237322400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 78497394743954323994656800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 74846353127956448460021600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 68476450734087814548530400 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 60724399707587307241149600 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 54549037025459784470863200 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (101 : ZMod 3218393184502127283780928801) ^ 52760544008231594816080800 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem prime_fortyNineAU_3620692332564893194253544901 : Nat.Prime 3620692332564893194253544901 := by
  apply lucas_primality 3620692332564893194253544901 (26 : ZMod 3620692332564893194253544901)
  · rw [← fortyNineAUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3620692332564893194253544901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyNineAU_2
      · exact prime_fortyNineAU_3
      · exact prime_fortyNineAU_5
      · exact prime_fortyNineAU_7
      · exact prime_fortyNineAU_11
      · exact prime_fortyNineAU_13
      · exact prime_fortyNineAU_17
      · exact prime_fortyNineAU_19
      · exact prime_fortyNineAU_23
      · exact prime_fortyNineAU_29
      · exact prime_fortyNineAU_31
      · exact prime_fortyNineAU_37
      · exact prime_fortyNineAU_41
      · exact prime_fortyNineAU_43
      · exact prime_fortyNineAU_47
      · exact prime_fortyNineAU_53
      · exact prime_fortyNineAU_59
      · exact prime_fortyNineAU_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 3620692332564893194253544901) ^ 1810346166282446597126772450 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 1206897444188297731417848300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 724138466512978638850708980 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 517241761794984742036220700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 329153848414990290386685900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 278514794812684091865657300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 212981901915581952603149700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 190562754345520694434397100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 157421405763691008445806300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 124851459743617006698398100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 116796526856932038524307900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 97856549528780897141987700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 88309569086948614493988900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 84202147268951004517524300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 77036007075848791367096700 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 68314949671035720646293300 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 61367666653642257529721100 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide
    · change (26 : ZMod 3620692332564893194253544901) ^ 59355612009260544168090900 ≠ 1
      rw [← fortyNineAUFastPow_eq_pow]
      decide

private theorem phi_fortyNineAU_57931077321038291108056718400 : Nat.totient 57931077321038291108056718400 = 7622997054508671329894400000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_7, prime_fortyNineAU_11, prime_fortyNineAU_13, prime_fortyNineAU_17, prime_fortyNineAU_19, prime_fortyNineAU_23, prime_fortyNineAU_29, prime_fortyNineAU_31, prime_fortyNineAU_37, prime_fortyNineAU_41, prime_fortyNineAU_43, prime_fortyNineAU_47, prime_fortyNineAU_53, prime_fortyNineAU_59, prime_fortyNineAU_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718401 : Nat.totient 57931077321038291108056718401 = 57931061979221330683970846352 := by
  rw [← show ((([(4148603, 1), (42045439, 1), (332116793722253, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_4148603, prime_fortyNineAU_42045439, prime_fortyNineAU_332116793722253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718402 : Nat.totient 57931077321038291108056718402 = 28794783287420212310846666640 := by
  rw [← show ((([(2, 1), (331, 1), (347, 1), (1189579, 1), (211997554864160267, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_331, prime_fortyNineAU_347, prime_fortyNineAU_1189579, prime_fortyNineAU_211997554864160267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718403 : Nat.totient 57931077321038291108056718403 = 38236818148548757867110208640 := by
  rw [← show ((([(3, 1), (173, 1), (239, 1), (1924976903, 1), (242616773704061, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_173, prime_fortyNineAU_239, prime_fortyNineAU_1924976903, prime_fortyNineAU_242616773704061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718404 : Nat.totient 57931077321038291108056718404 = 28965384401524337006322482400 := by
  rw [← show ((([(2, 2), (194863, 1), (5160101, 1), (14403367008001427, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_194863, prime_fortyNineAU_5160101, prime_fortyNineAU_14403367008001427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718405 : Nat.totient 57931077321038291108056718405 = 45956970611240974008164313600 := by
  rw [← show ((([(5, 1), (167, 1), (809, 1), (863, 1), (386051, 1), (257407460735179, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_167, prime_fortyNineAU_809, prime_fortyNineAU_863, prime_fortyNineAU_386051, prime_fortyNineAU_257407460735179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718406 : Nat.totient 57931077321038291108056718406 = 19310359029596897728834076544 := by
  rw [← show ((([(2, 1), (3, 1), (421049003, 1), (622326449, 1), (36847620883, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_421049003, prime_fortyNineAU_622326449, prime_fortyNineAU_36847620883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718407 : Nat.totient 57931077321038291108056718407 = 49654819639984945782942160152 := by
  rw [← show ((([(7, 1), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_7, prime_fortyNineAU_127487, prime_fortyNineAU_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718408 : Nat.totient 57931077321038291108056718408 = 28927244672157388374108813312 := by
  rw [← show ((([(2, 3), (757, 1), (951649, 1), (10051918134028374757, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_757, prime_fortyNineAU_951649, prime_fortyNineAU_10051918134028374757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718409 : Nat.totient 57931077321038291108056718409 = 38607340101517329727441341888 := by
  rw [← show ((([(3, 2), (2887, 1), (58892297, 1), (37858536207159359, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_2887, prime_fortyNineAU_58892297, prime_fortyNineAU_37858536207159359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718410 : Nat.totient 57931077321038291108056718410 = 23030102473399772845164096000 := by
  rw [← show ((([(2, 1), (5, 1), (191, 1), (1451, 1), (4759, 1), (82217, 1), (53423642393267, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_191, prime_fortyNineAU_1451, prime_fortyNineAU_4759, prime_fortyNineAU_82217, prime_fortyNineAU_53423642393267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718411 : Nat.totient 57931077321038291108056718411 = 52664596897748946430365792040 := by
  rw [← show ((([(11, 1), (2794079, 1), (1884864950003147601119, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_11, prime_fortyNineAU_2794079, prime_fortyNineAU_1884864950003147601119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718412 : Nat.totient 57931077321038291108056718412 = 19077666686338061790315055360 := by
  rw [← show ((([(2, 2), (3, 1), (83, 1), (548771, 1), (6995189, 1), (15151710392213, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_83, prime_fortyNineAU_548771, prime_fortyNineAU_6995189, prime_fortyNineAU_15151710392213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718413 : Nat.totient 57931077321038291108056718413 = 53273732974089690141301248000 := by
  rw [← show ((([(13, 1), (313, 1), (2699, 1), (5381, 1), (87383, 1), (11218404309401, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_13, prime_fortyNineAU_313, prime_fortyNineAU_2699, prime_fortyNineAU_5381, prime_fortyNineAU_87383, prime_fortyNineAU_11218404309401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718414 : Nat.totient 57931077321038291108056718414 = 24827536285484133589151969400 := by
  rw [← show ((([(2, 1), (7, 1), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_7, prime_fortyNineAU_363611, prime_fortyNineAU_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718415 : Nat.totient 57931077321038291108056718415 = 30896571492088910074015224576 := by
  rw [← show ((([(3, 1), (5, 1), (13393859, 1), (40003043, 1), (7208113129753, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_13393859, prime_fortyNineAU_40003043, prime_fortyNineAU_7208113129753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718416 : Nat.totient 57931077321038291108056718416 = 28965538660519145554028359200 := by
  rw [← show ((([(2, 4), (3620692332564893194253544901, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3620692332564893194253544901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718417 : Nat.totient 57931077321038291108056718417 = 54515381667974367268677120000 := by
  rw [← show ((([(17, 2), (7411, 1), (103991, 1), (524701, 1), (495711851953, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_17, prime_fortyNineAU_7411, prime_fortyNineAU_103991, prime_fortyNineAU_524701, prime_fortyNineAU_495711851953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718418 : Nat.totient 57931077321038291108056718418 = 19310359107012763702685572800 := by
  rw [← show ((([(2, 1), (3, 2), (3218393184502127283780928801, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_3218393184502127283780928801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718419 : Nat.totient 57931077321038291108056718419 = 54867675284095398098457484800 := by
  rw [← show ((([(19, 1), (6301, 1), (9649, 1), (57064603, 1), (878818959583, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_19, prime_fortyNineAU_6301, prime_fortyNineAU_9649, prime_fortyNineAU_57064603, prime_fortyNineAU_878818959583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718420 : Nat.totient 57931077321038291108056718420 = 23167435793300233132997057280 := by
  rw [← show ((([(2, 2), (5, 1), (4639, 1), (126639590279, 1), (4930463408441, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_4639, prime_fortyNineAU_126639590279, prime_fortyNineAU_4930463408441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718421 : Nat.totient 57931077321038291108056718421 = 32861841566887205800607771904 := by
  rw [← show ((([(3, 1), (7, 1), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_7, prime_fortyNineAU_137, prime_fortyNineAU_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718422 : Nat.totient 57931077321038291108056718422 = 26332307873199223230934872000 := by
  rw [← show ((([(2, 1), (11, 1), (2633230787319922323093487201, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_11, prime_fortyNineAU_2633230787319922323093487201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718423 : Nat.totient 57931077321038291108056718423 = 55371976245441459327659568864 := by
  rw [← show ((([(23, 1), (1373, 1), (616505944823, 1), (2975609680819, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_23, prime_fortyNineAU_1373, prime_fortyNineAU_616505944823, prime_fortyNineAU_2975609680819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718424 : Nat.totient 57931077321038291108056718424 = 19309647675824899059944847360 := by
  rw [← show ((([(2, 3), (3, 1), (27143, 1), (30038804161, 1), (2960464632287, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_27143, prime_fortyNineAU_30038804161, prime_fortyNineAU_2960464632287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718425 : Nat.totient 57931077321038291108056718425 = 46337436777331699712296070400 := by
  rw [← show ((([(5, 2), (6389, 1), (293507, 1), (3470581, 1), (356055796099, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_6389, prime_fortyNineAU_293507, prime_fortyNineAU_3470581, prime_fortyNineAU_356055796099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718426 : Nat.totient 57931077321038291108056718426 = 26737420302016455918822235200 := by
  rw [← show ((([(2, 1), (13, 1), (32189445165421, 1), (69218911573381, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_13, prime_fortyNineAU_32189445165421, prime_fortyNineAU_69218911573381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718427 : Nat.totient 57931077321038291108056718427 = 38382799033929248834921136000 := by
  rw [← show ((([(3, 3), (179, 1), (1733, 1), (4605692251, 1), (1501762763693, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_179, prime_fortyNineAU_1733, prime_fortyNineAU_4605692251, prime_fortyNineAU_1501762763693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718428 : Nat.totient 57931077321038291108056718428 = 24815995933407546098597978304 := by
  rw [← show ((([(2, 2), (7, 1), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_7, prime_fortyNineAU_3023, prime_fortyNineAU_7309, prime_fortyNineAU_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718429 : Nat.totient 57931077321038291108056718429 = 55874760578013504757837939200 := by
  rw [← show ((([(29, 1), (953, 1), (76804727, 1), (144114781, 1), (189375691, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_29, prime_fortyNineAU_953, prime_fortyNineAU_76804727, prime_fortyNineAU_144114781, prime_fortyNineAU_189375691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718430 : Nat.totient 57931077321038291108056718430 = 15448287285610210962148458240 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1931035910701276370268557281, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_1931035910701276370268557281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718431 : Nat.totient 57931077321038291108056718431 = 56062332891327378491667792000 := by
  rw [← show ((([(31, 1), (1868744429710912616388926401, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_31, prime_fortyNineAU_1868744429710912616388926401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718432 : Nat.totient 57931077321038291108056718432 = 28958898812456522293228800000 := by
  rw [← show ((([(2, 5), (4441, 1), (246361, 1), (1654660483466783251, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_4441, prime_fortyNineAU_246361, prime_fortyNineAU_1654660483466783251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718433 : Nat.totient 57931077321038291108056718433 = 34661829588239510589947851200 := by
  rw [← show ((([(3, 1), (11, 1), (79, 1), (9941, 1), (2235324097678346398259, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_11, prime_fortyNineAU_79, prime_fortyNineAU_9941, prime_fortyNineAU_2235324097678346398259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718434 : Nat.totient 57931077321038291108056718434 = 27261683433423811496922372864 := by
  rw [← show ((([(2, 1), (17, 1), (2316067309, 1), (735667399951481989, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_17, prime_fortyNineAU_2316067309, prime_fortyNineAU_735667399951481989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718435 : Nat.totient 57931077321038291108056718435 = 39277828347362077309860604416 := by
  rw [← show ((([(5, 1), (7, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_7, prime_fortyNineAU_89, prime_fortyNineAU_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718436 : Nat.totient 57931077321038291108056718436 = 19310359107012763702685572800 := by
  rw [← show ((([(2, 2), (3, 2), (1609196592251063641890464401, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_1609196592251063641890464401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718437 : Nat.totient 57931077321038291108056718437 = 56365372528570903998635838144 := by
  rw [← show ((([(37, 1), (8560197254309, 1), (182905223553389, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_37, prime_fortyNineAU_8560197254309, prime_fortyNineAU_182905223553389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718438 : Nat.totient 57931077321038291108056718438 = 27347381210134584429782286816 := by
  rw [← show ((([(2, 1), (19, 1), (293, 1), (53086172219, 1), (98011937938903, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_19, prime_fortyNineAU_293, prime_fortyNineAU_53086172219, prime_fortyNineAU_98011937938903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718439 : Nat.totient 57931077321038291108056718439 = 35393419680368717976366691296 := by
  rw [← show ((([(3, 1), (13, 1), (139, 1), (10686418985618574268226659, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_13, prime_fortyNineAU_139, prime_fortyNineAU_10686418985618574268226659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718440 : Nat.totient 57931077321038291108056718440 = 23112861697236870899666838784 := by
  rw [← show ((([(2, 3), (5, 1), (389, 1), (3723076948652846472240149, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_389, prime_fortyNineAU_3723076948652846472240149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718441 : Nat.totient 57931077321038291108056718441 = 56518124213576363785051088160 := by
  rw [← show ((([(41, 1), (27293573779, 1), (51768709983971419, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_41, prime_fortyNineAU_27293573779, prime_fortyNineAU_51768709983971419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718442 : Nat.totient 57931077321038291108056718442 = 16488227495127107506625879040 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_7, prime_fortyNineAU_263, prime_fortyNineAU_33811, prime_fortyNineAU_189853, prime_fortyNineAU_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718443 : Nat.totient 57931077321038291108056718443 = 56583842964735075035776329600 := by
  rw [← show ((([(43, 1), (1347234356303216072280388801, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_43, prime_fortyNineAU_1347234356303216072280388801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718444 : Nat.totient 57931077321038291108056718444 = 25971591326991014693524789440 := by
  rw [← show ((([(2, 2), (11, 2), (73, 1), (1639620664582766079136667, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_11, prime_fortyNineAU_73, prime_fortyNineAU_1639620664582766079136667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718445 : Nat.totient 57931077321038291108056718445 = 30896190294139602998016796800 := by
  rw [← show ((([(3, 2), (5, 1), (144899, 1), (180629, 1), (49186534555031551, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_144899, prime_fortyNineAU_180629, prime_fortyNineAU_49186534555031551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718446 : Nat.totient 57931077321038291108056718446 = 27426519817065127815314227200 := by
  rw [← show ((([(2, 1), (23, 1), (113, 1), (1187, 1), (2437, 1), (411583, 1), (9360771698401, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_23, prime_fortyNineAU_113, prime_fortyNineAU_1187, prime_fortyNineAU_2437, prime_fortyNineAU_411583, prime_fortyNineAU_9360771698401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718447 : Nat.totient 57931077321038291108056718447 = 56694724578168421615127730720 := by
  rw [← show ((([(47, 1), (15013, 1), (21494319307, 1), (3819641174311, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_47, prime_fortyNineAU_15013, prime_fortyNineAU_21494319307, prime_fortyNineAU_3819641174311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718448 : Nat.totient 57931077321038291108056718448 = 19310359107012763702685572800 := by
  rw [← show ((([(2, 4), (3, 1), (1206897444188297731417848301, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_1206897444188297731417848301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718449 : Nat.totient 57931077321038291108056718449 = 49163302769838416859041000064 := by
  rw [← show ((([(7, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_7, prime_fortyNineAU_103, prime_fortyNineAU_5009, prime_fortyNineAU_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718450 : Nat.totient 57931077321038291108056718450 = 23172430927909732878540355920 := by
  rw [← show ((([(2, 1), (5, 2), (45833121487, 1), (25279132400995087, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_45833121487, prime_fortyNineAU_25279132400995087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718451 : Nat.totient 57931077321038291108056718451 = 35802462988117531547513871360 := by
  rw [← show ((([(3, 1), (17, 1), (71, 1), (1039, 1), (15398114070722169843929, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_17, prime_fortyNineAU_71, prime_fortyNineAU_1039, prime_fortyNineAU_15398114070722169843929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718452 : Nat.totient 57931077321038291108056718452 = 26737420301773514356104949248 := by
  rw [← show ((([(2, 2), (13, 1), (109509651193, 1), (10173159781938457, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_13, prime_fortyNineAU_109509651193, prime_fortyNineAU_10173159781938457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718453 : Nat.totient 57931077321038291108056718453 = 55989701253703112951246917440 := by
  rw [← show ((([(53, 1), (67, 1), (7046861, 1), (2315075865962040023, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_53, prime_fortyNineAU_67, prime_fortyNineAU_7046861, prime_fortyNineAU_2315075865962040023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718454 : Nat.totient 57931077321038291108056718454 = 19274664520273200489702158400 := by
  rw [← show ((([(2, 1), (3, 4), (541, 1), (25290107, 1), (26136573949549541, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_541, prime_fortyNineAU_25290107, prime_fortyNineAU_26136573949549541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718455 : Nat.totient 57931077321038291108056718455 = 42131692597118757169495795200 := by
  rw [← show ((([(5, 1), (11, 1), (1053292314927968929237394881, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_11, prime_fortyNineAU_1053292314927968929237394881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718456 : Nat.totient 57931077321038291108056718456 = 24698964127992639288113000448 := by
  rw [← show ((([(2, 3), (7, 1), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_7, prime_fortyNineAU_193, prime_fortyNineAU_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718457 : Nat.totient 57931077321038291108056718457 = 36588048833892830228943613632 := by
  rw [← show ((([(3, 1), (19, 1), (81826801477, 1), (12420559908216013, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_19, prime_fortyNineAU_81826801477, prime_fortyNineAU_12420559908216013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718458 : Nat.totient 57931077321038291108056718458 = 27966718867703752175524559424 := by
  rw [← show ((([(2, 1), (29, 1), (3473947, 1), (434226839, 1), (662130753797, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_29, prime_fortyNineAU_3473947, prime_fortyNineAU_434226839, prime_fortyNineAU_662130753797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718459 : Nat.totient 57931077321038291108056718459 = 56935129642384080555430892160 := by
  rw [← show ((([(59, 1), (4049, 1), (5803704331, 1), (41783665617779, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_59, prime_fortyNineAU_4049, prime_fortyNineAU_5803704331, prime_fortyNineAU_41783665617779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718460 : Nat.totient 57931077321038291108056718460 = 15446812789943294343306801408 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (10477, 1), (43263636359, 1), (2130101955587, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_10477, prime_fortyNineAU_43263636359, prime_fortyNineAU_2130101955587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718461 : Nat.totient 57931077321038291108056718461 = 56695048898013832041636436800 := by
  rw [← show ((([(61, 1), (199, 1), (834575807771, 1), (5718246885269, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_61, prime_fortyNineAU_199, prime_fortyNineAU_834575807771, prime_fortyNineAU_5718246885269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718462 : Nat.totient 57931077321038291108056718462 = 28029087169518247740734731200 := by
  rw [← show ((([(2, 1), (31, 1), (14087, 1), (313471, 1), (211594332736121513, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_31, prime_fortyNineAU_14087, prime_fortyNineAU_313471, prime_fortyNineAU_211594332736121513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718463 : Nat.totient 57931077321038291108056718463 = 33103472754879023490318124800 := by
  rw [← show ((([(3, 2), (7, 1), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_7, prime_fortyNineAU_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718464 : Nat.totient 57931077321038291108056718464 = 28965538660519145554028359168 := by
  rw [← show ((([(2, 7), (452586541570611649281693113, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_452586541570611649281693113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718465 : Nat.totient 57931077321038291108056718465 = 42507371365624535300770904064 := by
  rw [← show ((([(5, 1), (13, 1), (157, 1), (2744563, 1), (17972329, 1), (115085611999, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_13, prime_fortyNineAU_157, prime_fortyNineAU_2744563, prime_fortyNineAU_17972329, prime_fortyNineAU_115085611999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718466 : Nat.totient 57931077321038291108056718466 = 17554871915439355007395398080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (655504518509, 1), (1339035156873989, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_11, prime_fortyNineAU_655504518509, prime_fortyNineAU_1339035156873989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718467 : Nat.totient 57931077321038291108056718467 = 57833341260023003307228430848 := by
  rw [← show ((([(593, 1), (1298723, 1), (75221221193696524753, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_593, prime_fortyNineAU_1298723, prime_fortyNineAU_75221221193696524753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718468 : Nat.totient 57931077321038291108056718468 = 27261683443590091306367698944 := by
  rw [← show ((([(2, 2), (17, 1), (16991844937, 1), (50137440096763273, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_17, prime_fortyNineAU_16991844937, prime_fortyNineAU_50137440096763273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718469 : Nat.totient 57931077321038291108056718469 = 36941556552546156648615878400 := by
  rw [← show ((([(3, 1), (23, 1), (839580830739685378377633601, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_23, prime_fortyNineAU_839580830739685378377633601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718470 : Nat.totient 57931077321038291108056718470 = 19656949860452231123242291200 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_7, prime_fortyNineAU_97, prime_fortyNineAU_72973, prime_fortyNineAU_195271, prime_fortyNineAU_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718471 : Nat.totient 57931077321038291108056718471 = 57931077043005416824962742200 := by
  rw [← show ((([(208360531, 1), (278032874282885615741, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_208360531, prime_fortyNineAU_278032874282885615741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718472 : Nat.totient 57931077321038291108056718472 = 19310358929046992719624999296 := by
  rw [← show ((([(2, 3), (3, 2), (108506029, 1), (7415240457519017869, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_108506029, prime_fortyNineAU_7415240457519017869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718473 : Nat.totient 57931077321038291108056718473 = 57678103184265198133785728208 := by
  rw [← show ((([(229, 1), (252974136773092974270990037, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_229, prime_fortyNineAU_252974136773092974270990037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718474 : Nat.totient 57931077321038291108056718474 = 27875508569249464711855346688 := by
  rw [← show ((([(2, 1), (37, 1), (109, 1), (659, 1), (4463, 1), (204944669, 1), (11915285693, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_37, prime_fortyNineAU_109, prime_fortyNineAU_659, prime_fortyNineAU_4463, prime_fortyNineAU_204944669, prime_fortyNineAU_11915285693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718475 : Nat.totient 57931077321038291108056718475 = 30863772546655417886158224000 := by
  rw [← show ((([(3, 1), (5, 2), (947, 1), (175079, 1), (4658716739810258701, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_947, prime_fortyNineAU_175079, prime_fortyNineAU_4658716739810258701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718476 : Nat.totient 57931077321038291108056718476 = 27375544891564633984236811344 := by
  rw [← show ((([(2, 2), (19, 1), (419, 1), (1819214838620722619898779, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_19, prime_fortyNineAU_419, prime_fortyNineAU_1819214838620722619898779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718477 : Nat.totient 57931077321038291108056718477 = 45141099211198668395888352000 := by
  rw [← show ((([(7, 1), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_7, prime_fortyNineAU_11, prime_fortyNineAU_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718478 : Nat.totient 57931077321038291108056718478 = 17684241837207735233598336000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (127, 1), (70201, 1), (178261, 1), (467319221172283, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_13, prime_fortyNineAU_127, prime_fortyNineAU_70201, prime_fortyNineAU_178261, prime_fortyNineAU_467319221172283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718479 : Nat.totient 57931077321038291108056718479 = 57927827695340134475358655176 := by
  rw [← show ((([(17827, 1), (3249625698156632698045477, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_17827, prime_fortyNineAU_3249625698156632698045477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718480 : Nat.totient 57931077321038291108056718480 = 23172430928415316443222687360 := by
  rw [← show ((([(2, 4), (5, 1), (724138466512978638850708981, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_724138466512978638850708981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718481 : Nat.totient 57931077321038291108056718481 = 38620718214011461180144018944 := by
  rw [← show ((([(3, 3), (2755349978497, 1), (778701607084099, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_2755349978497, prime_fortyNineAU_778701607084099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718482 : Nat.totient 57931077321038291108056718482 = 28259062107219035293666526080 := by
  rw [← show ((([(2, 1), (41, 1), (46746322157, 1), (15112986863925893, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_41, prime_fortyNineAU_46746322157, prime_fortyNineAU_15112986863925893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718483 : Nat.totient 57931077321038291108056718483 = 57893038519750278447794044000 := by
  rw [← show ((([(1523, 1), (43713101, 1), (870161943018760421, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_1523, prime_fortyNineAU_43713101, prime_fortyNineAU_870161943018760421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718484 : Nat.totient 57931077321038291108056718484 = 16354891990877622562043289600 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_7, prime_fortyNineAU_131, prime_fortyNineAU_233, prime_fortyNineAU_550990241, prime_fortyNineAU_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718485 : Nat.totient 57931077321038291108056718485 = 43618693511692093347482930176 := by
  rw [← show ((([(5, 1), (17, 1), (70456593989, 1), (9673219319064269, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_17, prime_fortyNineAU_70456593989, prime_fortyNineAU_9673219319064269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718486 : Nat.totient 57931077321038291108056718486 = 28011800385497906463897600000 := by
  rw [← show ((([(2, 1), (43, 1), (101, 1), (10202561, 1), (89497481, 1), (7304185061, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_43, prime_fortyNineAU_101, prime_fortyNineAU_10202561, prime_fortyNineAU_89497481, prime_fortyNineAU_7304185061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718487 : Nat.totient 57931077321038291108056718487 = 37288969310093612667254899200 := by
  rw [← show ((([(3, 1), (29, 1), (665874451965957369058123201, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_29, prime_fortyNineAU_665874451965957369058123201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718488 : Nat.totient 57931077321038291108056718488 = 26086211537935679088589682080 := by
  rw [← show ((([(2, 3), (11, 1), (107, 1), (6152408381588603558629643, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_11, prime_fortyNineAU_107, prime_fortyNineAU_6152408381588603558629643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718489 : Nat.totient 57931077321038291108056718489 = 57758331981929716309394803200 := by
  rw [← show ((([(431, 1), (2111, 1), (5273, 1), (12075033107354015473, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_431, prime_fortyNineAU_2111, prime_fortyNineAU_5273, prime_fortyNineAU_12075033107354015473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718490 : Nat.totient 57931077321038291108056718490 = 15448287285603127576767879168 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (2197277019473, 1), (292943780504657, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_5, prime_fortyNineAU_2197277019473, prime_fortyNineAU_292943780504657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718491 : Nat.totient 57931077321038291108056718491 = 45831166576234426042936431840 := by
  rw [← show ((([(7, 1), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_7, prime_fortyNineAU_13, prime_fortyNineAU_10391, prime_fortyNineAU_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718492 : Nat.totient 57931077321038291108056718492 = 27513788248511328398342602752 := by
  rw [← show ((([(2, 2), (23, 1), (163, 1), (1249, 1), (99689, 1), (343543, 1), (90311985749, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_23, prime_fortyNineAU_163, prime_fortyNineAU_1249, prime_fortyNineAU_99689, prime_fortyNineAU_343543, prime_fortyNineAU_90311985749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718493 : Nat.totient 57931077321038291108056718493 = 37117166668206079779736888320 := by
  rw [← show ((([(3, 1), (31, 1), (149, 1), (5393, 1), (775196793635843554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_31, prime_fortyNineAU_149, prime_fortyNineAU_5393, prime_fortyNineAU_775196793635843554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718494 : Nat.totient 57931077321038291108056718494 = 28349250603912355223091585600 := by
  rw [← show ((([(2, 1), (47, 1), (616288056606790330936773601, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_47, prime_fortyNineAU_616288056606790330936773601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718495 : Nat.totient 57931077321038291108056718495 = 43376080201156494623008419840 := by
  rw [← show ((([(5, 1), (19, 1), (83, 1), (73061, 1), (50640673, 1), (1985751166879, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_5, prime_fortyNineAU_19, prime_fortyNineAU_83, prime_fortyNineAU_73061, prime_fortyNineAU_50640673, prime_fortyNineAU_1985751166879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718496 : Nat.totient 57931077321038291108056718496 = 19281087720456387010419354624 := by
  rw [← show ((([(2, 5), (3, 1), (1229, 1), (1423, 1), (345051237226243542653, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_3, prime_fortyNineAU_1229, prime_fortyNineAU_1423, prime_fortyNineAU_345051237226243542653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718497 : Nat.totient 57931077321038291108056718497 = 57931077320891963790304651396 := by
  rw [← show ((([(395901701399, 1), (146326921850365703, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_395901701399, prime_fortyNineAU_146326921850365703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718498 : Nat.totient 57931077321038291108056718498 = 24827604545852314306052656200 := by
  rw [← show ((([(2, 1), (7, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_7, prime_fortyNineAU_1222615931, prime_fortyNineAU_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718499 : Nat.totient 57931077321038291108056718499 = 35109743830932297641246496000 := by
  rw [← show ((([(3, 2), (11, 1), (585162397182204960687441601, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_3, prime_fortyNineAU_11, prime_fortyNineAU_585162397182204960687441601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyNineAU_57931077321038291108056718500 : Nat.totient 57931077321038291108056718500 = 23172430752371609035334220000 := by
  rw [← show ((([(2, 2), (5, 3), (131628851, 1), (880218536907813487, 1)] : List FactorBlock).map factorBlockValue).prod) = 57931077321038291108056718500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyNineAU_2, prime_fortyNineAU_5, prime_fortyNineAU_131628851, prime_fortyNineAU_880218536907813487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyNineAU : certifiedKill 1 57931077321038291108056718399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyNineAU_57931077321038291108056718400, phi_fortyNineAU_57931077321038291108056718401, phi_fortyNineAU_57931077321038291108056718402,
    phi_fortyNineAU_57931077321038291108056718403, phi_fortyNineAU_57931077321038291108056718404, phi_fortyNineAU_57931077321038291108056718405,
    phi_fortyNineAU_57931077321038291108056718406, phi_fortyNineAU_57931077321038291108056718407, phi_fortyNineAU_57931077321038291108056718408,
    phi_fortyNineAU_57931077321038291108056718409, phi_fortyNineAU_57931077321038291108056718410, phi_fortyNineAU_57931077321038291108056718411,
    phi_fortyNineAU_57931077321038291108056718412, phi_fortyNineAU_57931077321038291108056718413, phi_fortyNineAU_57931077321038291108056718414,
    phi_fortyNineAU_57931077321038291108056718415, phi_fortyNineAU_57931077321038291108056718416, phi_fortyNineAU_57931077321038291108056718417,
    phi_fortyNineAU_57931077321038291108056718418, phi_fortyNineAU_57931077321038291108056718419, phi_fortyNineAU_57931077321038291108056718420,
    phi_fortyNineAU_57931077321038291108056718421, phi_fortyNineAU_57931077321038291108056718422, phi_fortyNineAU_57931077321038291108056718423,
    phi_fortyNineAU_57931077321038291108056718424, phi_fortyNineAU_57931077321038291108056718425, phi_fortyNineAU_57931077321038291108056718426,
    phi_fortyNineAU_57931077321038291108056718427, phi_fortyNineAU_57931077321038291108056718428, phi_fortyNineAU_57931077321038291108056718429,
    phi_fortyNineAU_57931077321038291108056718430, phi_fortyNineAU_57931077321038291108056718431, phi_fortyNineAU_57931077321038291108056718432,
    phi_fortyNineAU_57931077321038291108056718433, phi_fortyNineAU_57931077321038291108056718434, phi_fortyNineAU_57931077321038291108056718435,
    phi_fortyNineAU_57931077321038291108056718436, phi_fortyNineAU_57931077321038291108056718437, phi_fortyNineAU_57931077321038291108056718438,
    phi_fortyNineAU_57931077321038291108056718439, phi_fortyNineAU_57931077321038291108056718440, phi_fortyNineAU_57931077321038291108056718441,
    phi_fortyNineAU_57931077321038291108056718442, phi_fortyNineAU_57931077321038291108056718443, phi_fortyNineAU_57931077321038291108056718444,
    phi_fortyNineAU_57931077321038291108056718445, phi_fortyNineAU_57931077321038291108056718446, phi_fortyNineAU_57931077321038291108056718447,
    phi_fortyNineAU_57931077321038291108056718448, phi_fortyNineAU_57931077321038291108056718449, phi_fortyNineAU_57931077321038291108056718450,
    phi_fortyNineAU_57931077321038291108056718451, phi_fortyNineAU_57931077321038291108056718452, phi_fortyNineAU_57931077321038291108056718453,
    phi_fortyNineAU_57931077321038291108056718454, phi_fortyNineAU_57931077321038291108056718455, phi_fortyNineAU_57931077321038291108056718456,
    phi_fortyNineAU_57931077321038291108056718457, phi_fortyNineAU_57931077321038291108056718458, phi_fortyNineAU_57931077321038291108056718459,
    phi_fortyNineAU_57931077321038291108056718460, phi_fortyNineAU_57931077321038291108056718461, phi_fortyNineAU_57931077321038291108056718462,
    phi_fortyNineAU_57931077321038291108056718463, phi_fortyNineAU_57931077321038291108056718464, phi_fortyNineAU_57931077321038291108056718465,
    phi_fortyNineAU_57931077321038291108056718466, phi_fortyNineAU_57931077321038291108056718467, phi_fortyNineAU_57931077321038291108056718468,
    phi_fortyNineAU_57931077321038291108056718469, phi_fortyNineAU_57931077321038291108056718470, phi_fortyNineAU_57931077321038291108056718471,
    phi_fortyNineAU_57931077321038291108056718472, phi_fortyNineAU_57931077321038291108056718473, phi_fortyNineAU_57931077321038291108056718474,
    phi_fortyNineAU_57931077321038291108056718475, phi_fortyNineAU_57931077321038291108056718476, phi_fortyNineAU_57931077321038291108056718477,
    phi_fortyNineAU_57931077321038291108056718478, phi_fortyNineAU_57931077321038291108056718479, phi_fortyNineAU_57931077321038291108056718480,
    phi_fortyNineAU_57931077321038291108056718481, phi_fortyNineAU_57931077321038291108056718482, phi_fortyNineAU_57931077321038291108056718483,
    phi_fortyNineAU_57931077321038291108056718484, phi_fortyNineAU_57931077321038291108056718485, phi_fortyNineAU_57931077321038291108056718486,
    phi_fortyNineAU_57931077321038291108056718487, phi_fortyNineAU_57931077321038291108056718488, phi_fortyNineAU_57931077321038291108056718489,
    phi_fortyNineAU_57931077321038291108056718490, phi_fortyNineAU_57931077321038291108056718491, phi_fortyNineAU_57931077321038291108056718492,
    phi_fortyNineAU_57931077321038291108056718493, phi_fortyNineAU_57931077321038291108056718494, phi_fortyNineAU_57931077321038291108056718495,
    phi_fortyNineAU_57931077321038291108056718496, phi_fortyNineAU_57931077321038291108056718497, phi_fortyNineAU_57931077321038291108056718498,
    phi_fortyNineAU_57931077321038291108056718499, phi_fortyNineAU_57931077321038291108056718500]

end TotientTailPeriodKiller
end Erdos249257
