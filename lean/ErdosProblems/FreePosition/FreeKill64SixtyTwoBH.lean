import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 62P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyTwoBHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyTwoBHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyTwoBHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyTwoBHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyTwoBHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyTwoBHFastPow a n * sixtyTwoBHFastPow a n * a
        else sixtyTwoBHFastPow a n * sixtyTwoBHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyTwoBH_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyTwoBH_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyTwoBH_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyTwoBH_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyTwoBH_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyTwoBH_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyTwoBH_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyTwoBH_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyTwoBH_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyTwoBH_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyTwoBH_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyTwoBH_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyTwoBH_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyTwoBH_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyTwoBH_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyTwoBH_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyTwoBH_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyTwoBH_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyTwoBH_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyTwoBH_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyTwoBH_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyTwoBH_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyTwoBH_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyTwoBH_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyTwoBH_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyTwoBH_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyTwoBH_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyTwoBH_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyTwoBH_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyTwoBH_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyTwoBH_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyTwoBH_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyTwoBH_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyTwoBH_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyTwoBH_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyTwoBH_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtyTwoBH_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyTwoBH_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyTwoBH_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyTwoBH_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyTwoBH_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyTwoBH_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyTwoBH_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyTwoBH_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyTwoBH_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyTwoBH_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyTwoBH_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixtyTwoBH_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyTwoBH_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyTwoBH_233 : Nat.Prime 233 := by norm_num
private theorem prime_sixtyTwoBH_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyTwoBH_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyTwoBH_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtyTwoBH_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyTwoBH_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyTwoBH_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyTwoBH_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtyTwoBH_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyTwoBH_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyTwoBH_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtyTwoBH_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtyTwoBH_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyTwoBH_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtyTwoBH_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyTwoBH_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyTwoBH_349 : Nat.Prime 349 := by norm_num
private theorem prime_sixtyTwoBH_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtyTwoBH_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtyTwoBH_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixtyTwoBH_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyTwoBH_397 : Nat.Prime 397 := by norm_num
private theorem prime_sixtyTwoBH_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyTwoBH_421 : Nat.Prime 421 := by norm_num
private theorem prime_sixtyTwoBH_439 : Nat.Prime 439 := by norm_num
private theorem prime_sixtyTwoBH_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtyTwoBH_463 : Nat.Prime 463 := by norm_num
private theorem prime_sixtyTwoBH_467 : Nat.Prime 467 := by norm_num
private theorem prime_sixtyTwoBH_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyTwoBH_487 : Nat.Prime 487 := by norm_num
private theorem prime_sixtyTwoBH_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixtyTwoBH_503 : Nat.Prime 503 := by norm_num
private theorem prime_sixtyTwoBH_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyTwoBH_547 : Nat.Prime 547 := by norm_num
private theorem prime_sixtyTwoBH_563 : Nat.Prime 563 := by norm_num
private theorem prime_sixtyTwoBH_569 : Nat.Prime 569 := by norm_num
private theorem prime_sixtyTwoBH_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtyTwoBH_587 : Nat.Prime 587 := by norm_num
private theorem prime_sixtyTwoBH_593 : Nat.Prime 593 := by norm_num
private theorem prime_sixtyTwoBH_599 : Nat.Prime 599 := by norm_num
private theorem prime_sixtyTwoBH_613 : Nat.Prime 613 := by norm_num
private theorem prime_sixtyTwoBH_619 : Nat.Prime 619 := by norm_num
private theorem prime_sixtyTwoBH_631 : Nat.Prime 631 := by norm_num
private theorem prime_sixtyTwoBH_643 : Nat.Prime 643 := by norm_num
private theorem prime_sixtyTwoBH_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixtyTwoBH_659 : Nat.Prime 659 := by norm_num
private theorem prime_sixtyTwoBH_677 : Nat.Prime 677 := by norm_num
private theorem prime_sixtyTwoBH_691 : Nat.Prime 691 := by norm_num
private theorem prime_sixtyTwoBH_709 : Nat.Prime 709 := by norm_num
private theorem prime_sixtyTwoBH_757 : Nat.Prime 757 := by norm_num
private theorem prime_sixtyTwoBH_769 : Nat.Prime 769 := by norm_num
private theorem prime_sixtyTwoBH_773 : Nat.Prime 773 := by norm_num
private theorem prime_sixtyTwoBH_787 : Nat.Prime 787 := by norm_num
private theorem prime_sixtyTwoBH_811 : Nat.Prime 811 := by norm_num
private theorem prime_sixtyTwoBH_821 : Nat.Prime 821 := by norm_num
private theorem prime_sixtyTwoBH_829 : Nat.Prime 829 := by norm_num
private theorem prime_sixtyTwoBH_859 : Nat.Prime 859 := by norm_num
private theorem prime_sixtyTwoBH_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixtyTwoBH_883 : Nat.Prime 883 := by norm_num
private theorem prime_sixtyTwoBH_929 : Nat.Prime 929 := by norm_num
private theorem prime_sixtyTwoBH_991 : Nat.Prime 991 := by norm_num
private theorem prime_sixtyTwoBH_997 : Nat.Prime 997 := by norm_num
private theorem prime_sixtyTwoBH_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_sixtyTwoBH_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyTwoBH_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_sixtyTwoBH_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_sixtyTwoBH_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_sixtyTwoBH_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_sixtyTwoBH_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_sixtyTwoBH_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_sixtyTwoBH_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_sixtyTwoBH_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_sixtyTwoBH_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtyTwoBH_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_sixtyTwoBH_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_sixtyTwoBH_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_sixtyTwoBH_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_sixtyTwoBH_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_sixtyTwoBH_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_sixtyTwoBH_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_sixtyTwoBH_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_sixtyTwoBH_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_sixtyTwoBH_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_sixtyTwoBH_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_sixtyTwoBH_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_sixtyTwoBH_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_sixtyTwoBH_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_sixtyTwoBH_1657 : Nat.Prime 1657 := by norm_num
private theorem prime_sixtyTwoBH_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_sixtyTwoBH_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_sixtyTwoBH_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_sixtyTwoBH_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_sixtyTwoBH_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_sixtyTwoBH_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_sixtyTwoBH_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_sixtyTwoBH_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_sixtyTwoBH_2203 : Nat.Prime 2203 := by norm_num
private theorem prime_sixtyTwoBH_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_sixtyTwoBH_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_sixtyTwoBH_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_sixtyTwoBH_2357 : Nat.Prime 2357 := by norm_num
private theorem prime_sixtyTwoBH_2503 : Nat.Prime 2503 := by norm_num
private theorem prime_sixtyTwoBH_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_sixtyTwoBH_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_sixtyTwoBH_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_sixtyTwoBH_2953 : Nat.Prime 2953 := by norm_num
private theorem prime_sixtyTwoBH_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_sixtyTwoBH_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_sixtyTwoBH_3169 : Nat.Prime 3169 := by norm_num
private theorem prime_sixtyTwoBH_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_sixtyTwoBH_3461 : Nat.Prime 3461 := by norm_num
private theorem prime_sixtyTwoBH_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_sixtyTwoBH_3581 : Nat.Prime 3581 := by norm_num
private theorem prime_sixtyTwoBH_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_sixtyTwoBH_3613 : Nat.Prime 3613 := by norm_num
private theorem prime_sixtyTwoBH_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_sixtyTwoBH_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_sixtyTwoBH_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_sixtyTwoBH_3727 : Nat.Prime 3727 := by norm_num
private theorem prime_sixtyTwoBH_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_sixtyTwoBH_3797 : Nat.Prime 3797 := by norm_num
private theorem prime_sixtyTwoBH_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_sixtyTwoBH_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_sixtyTwoBH_4079 : Nat.Prime 4079 := by norm_num
private theorem prime_sixtyTwoBH_4129 : Nat.Prime 4129 := by norm_num
private theorem prime_sixtyTwoBH_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_sixtyTwoBH_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_sixtyTwoBH_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_sixtyTwoBH_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_sixtyTwoBH_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_sixtyTwoBH_5297 : Nat.Prime 5297 := by norm_num
private theorem prime_sixtyTwoBH_5309 : Nat.Prime 5309 := by norm_num
private theorem prime_sixtyTwoBH_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_sixtyTwoBH_5657 : Nat.Prime 5657 := by norm_num
private theorem prime_sixtyTwoBH_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_sixtyTwoBH_5981 : Nat.Prime 5981 := by norm_num
private theorem prime_sixtyTwoBH_6197 : Nat.Prime 6197 := by norm_num
private theorem prime_sixtyTwoBH_6269 : Nat.Prime 6269 := by norm_num
private theorem prime_sixtyTwoBH_6359 : Nat.Prime 6359 := by norm_num
private theorem prime_sixtyTwoBH_6367 : Nat.Prime 6367 := by norm_num
private theorem prime_sixtyTwoBH_6373 : Nat.Prime 6373 := by norm_num
private theorem prime_sixtyTwoBH_6703 : Nat.Prime 6703 := by norm_num
private theorem prime_sixtyTwoBH_7411 : Nat.Prime 7411 := by norm_num
private theorem prime_sixtyTwoBH_7561 : Nat.Prime 7561 := by norm_num
private theorem prime_sixtyTwoBH_7577 : Nat.Prime 7577 := by norm_num
private theorem prime_sixtyTwoBH_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_sixtyTwoBH_7877 : Nat.Prime 7877 := by norm_num
private theorem prime_sixtyTwoBH_8009 : Nat.Prime 8009 := by norm_num
private theorem prime_sixtyTwoBH_8161 : Nat.Prime 8161 := by norm_num
private theorem prime_sixtyTwoBH_8513 : Nat.Prime 8513 := by norm_num
private theorem prime_sixtyTwoBH_8573 : Nat.Prime 8573 := by norm_num
private theorem prime_sixtyTwoBH_8609 : Nat.Prime 8609 := by norm_num
private theorem prime_sixtyTwoBH_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_sixtyTwoBH_9623 : Nat.Prime 9623 := by norm_num
private theorem prime_sixtyTwoBH_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_sixtyTwoBH_10133 : Nat.Prime 10133 := by norm_num
private theorem prime_sixtyTwoBH_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_sixtyTwoBH_10601 : Nat.Prime 10601 := by norm_num
private theorem prime_sixtyTwoBH_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_sixtyTwoBH_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_sixtyTwoBH_10837 : Nat.Prime 10837 := by norm_num
private theorem prime_sixtyTwoBH_11369 : Nat.Prime 11369 := by norm_num
private theorem prime_sixtyTwoBH_11617 : Nat.Prime 11617 := by norm_num
private theorem prime_sixtyTwoBH_11701 : Nat.Prime 11701 := by norm_num
private theorem prime_sixtyTwoBH_13219 : Nat.Prime 13219 := by norm_num
private theorem prime_sixtyTwoBH_13327 : Nat.Prime 13327 := by norm_num
private theorem prime_sixtyTwoBH_14557 : Nat.Prime 14557 := by norm_num
private theorem prime_sixtyTwoBH_14629 : Nat.Prime 14629 := by norm_num
private theorem prime_sixtyTwoBH_14713 : Nat.Prime 14713 := by norm_num
private theorem prime_sixtyTwoBH_14771 : Nat.Prime 14771 := by norm_num
private theorem prime_sixtyTwoBH_15391 : Nat.Prime 15391 := by norm_num
private theorem prime_sixtyTwoBH_15991 : Nat.Prime 15991 := by norm_num
private theorem prime_sixtyTwoBH_16067 : Nat.Prime 16067 := by norm_num
private theorem prime_sixtyTwoBH_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_sixtyTwoBH_16699 : Nat.Prime 16699 := by norm_num
private theorem prime_sixtyTwoBH_16829 : Nat.Prime 16829 := by norm_num
private theorem prime_sixtyTwoBH_17077 : Nat.Prime 17077 := by norm_num
private theorem prime_sixtyTwoBH_18919 : Nat.Prime 18919 := by norm_num
private theorem prime_sixtyTwoBH_19489 : Nat.Prime 19489 := by norm_num
private theorem prime_sixtyTwoBH_20719 : Nat.Prime 20719 := by norm_num
private theorem prime_sixtyTwoBH_21277 : Nat.Prime 21277 := by norm_num
private theorem prime_sixtyTwoBH_23201 : Nat.Prime 23201 := by norm_num
private theorem prime_sixtyTwoBH_24767 : Nat.Prime 24767 := by norm_num
private theorem prime_sixtyTwoBH_26141 : Nat.Prime 26141 := by norm_num
private theorem prime_sixtyTwoBH_26339 : Nat.Prime 26339 := by norm_num
private theorem prime_sixtyTwoBH_27011 : Nat.Prime 27011 := by norm_num
private theorem prime_sixtyTwoBH_27211 : Nat.Prime 27211 := by norm_num
private theorem prime_sixtyTwoBH_27527 : Nat.Prime 27527 := by norm_num
private theorem prime_sixtyTwoBH_27803 : Nat.Prime 27803 := by norm_num
private theorem prime_sixtyTwoBH_32353 : Nat.Prime 32353 := by norm_num
private theorem prime_sixtyTwoBH_33119 : Nat.Prime 33119 := by norm_num
private theorem prime_sixtyTwoBH_34843 : Nat.Prime 34843 := by norm_num
private theorem prime_sixtyTwoBH_35323 : Nat.Prime 35323 := by norm_num
private theorem prime_sixtyTwoBH_36563 : Nat.Prime 36563 := by norm_num
private theorem prime_sixtyTwoBH_37189 : Nat.Prime 37189 := by norm_num
private theorem prime_sixtyTwoBH_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_sixtyTwoBH_37507 : Nat.Prime 37507 := by norm_num
private theorem prime_sixtyTwoBH_37781 : Nat.Prime 37781 := by norm_num
private theorem prime_sixtyTwoBH_37987 : Nat.Prime 37987 := by norm_num
private theorem prime_sixtyTwoBH_38543 : Nat.Prime 38543 := by norm_num
private theorem prime_sixtyTwoBH_40543 : Nat.Prime 40543 := by norm_num
private theorem prime_sixtyTwoBH_41177 : Nat.Prime 41177 := by norm_num
private theorem prime_sixtyTwoBH_42443 : Nat.Prime 42443 := by norm_num
private theorem prime_sixtyTwoBH_43781 : Nat.Prime 43781 := by norm_num
private theorem prime_sixtyTwoBH_45317 : Nat.Prime 45317 := by norm_num
private theorem prime_sixtyTwoBH_45757 : Nat.Prime 45757 := by norm_num
private theorem prime_sixtyTwoBH_46049 : Nat.Prime 46049 := by norm_num
private theorem prime_sixtyTwoBH_47059 : Nat.Prime 47059 := by norm_num
private theorem prime_sixtyTwoBH_47087 : Nat.Prime 47087 := by norm_num
private theorem prime_sixtyTwoBH_47111 : Nat.Prime 47111 := by norm_num
private theorem prime_sixtyTwoBH_47657 : Nat.Prime 47657 := by norm_num
private theorem prime_sixtyTwoBH_48869 : Nat.Prime 48869 := by norm_num
private theorem prime_sixtyTwoBH_50593 : Nat.Prime 50593 := by norm_num
private theorem prime_sixtyTwoBH_51827 : Nat.Prime 51827 := by norm_num
private theorem prime_sixtyTwoBH_51869 : Nat.Prime 51869 := by norm_num
private theorem prime_sixtyTwoBH_55501 : Nat.Prime 55501 := by norm_num
private theorem prime_sixtyTwoBH_56167 : Nat.Prime 56167 := by norm_num
private theorem prime_sixtyTwoBH_56663 : Nat.Prime 56663 := by norm_num
private theorem prime_sixtyTwoBH_57119 : Nat.Prime 57119 := by norm_num
private theorem prime_sixtyTwoBH_60383 : Nat.Prime 60383 := by norm_num
private theorem prime_sixtyTwoBH_61781 : Nat.Prime 61781 := by norm_num
private theorem prime_sixtyTwoBH_66071 : Nat.Prime 66071 := by norm_num
private theorem prime_sixtyTwoBH_66587 : Nat.Prime 66587 := by norm_num
private theorem prime_sixtyTwoBH_67829 : Nat.Prime 67829 := by norm_num
private theorem prime_sixtyTwoBH_68141 : Nat.Prime 68141 := by norm_num
private theorem prime_sixtyTwoBH_68903 : Nat.Prime 68903 := by norm_num
private theorem prime_sixtyTwoBH_70373 : Nat.Prime 70373 := by norm_num
private theorem prime_sixtyTwoBH_70991 : Nat.Prime 70991 := by norm_num
private theorem prime_sixtyTwoBH_71171 : Nat.Prime 71171 := by norm_num
private theorem prime_sixtyTwoBH_72613 : Nat.Prime 72613 := by norm_num
private theorem prime_sixtyTwoBH_76091 : Nat.Prime 76091 := by norm_num
private theorem prime_sixtyTwoBH_80627 : Nat.Prime 80627 := by norm_num
private theorem prime_sixtyTwoBH_83873 : Nat.Prime 83873 := by norm_num
private theorem prime_sixtyTwoBH_83891 : Nat.Prime 83891 := by norm_num
private theorem prime_sixtyTwoBH_85643 : Nat.Prime 85643 := by norm_num
private theorem prime_sixtyTwoBH_85717 : Nat.Prime 85717 := by norm_num
private theorem prime_sixtyTwoBH_87511 : Nat.Prime 87511 := by norm_num
private theorem prime_sixtyTwoBH_89821 : Nat.Prime 89821 := by norm_num
private theorem prime_sixtyTwoBH_90071 : Nat.Prime 90071 := by norm_num
private theorem prime_sixtyTwoBH_92399 : Nat.Prime 92399 := by norm_num
private theorem prime_sixtyTwoBH_94321 : Nat.Prime 94321 := by norm_num
private theorem prime_sixtyTwoBH_96997 : Nat.Prime 96997 := by norm_num
private theorem prime_sixtyTwoBH_102233 : Nat.Prime 102233 := by norm_num
private theorem prime_sixtyTwoBH_111623 : Nat.Prime 111623 := by norm_num
private theorem prime_sixtyTwoBH_114847 : Nat.Prime 114847 := by norm_num
private theorem prime_sixtyTwoBH_124433 : Nat.Prime 124433 := by norm_num
private theorem prime_sixtyTwoBH_126499 : Nat.Prime 126499 := by norm_num
private theorem prime_sixtyTwoBH_127541 : Nat.Prime 127541 := by norm_num
private theorem prime_sixtyTwoBH_132241 : Nat.Prime 132241 := by norm_num
private theorem prime_sixtyTwoBH_135671 : Nat.Prime 135671 := by norm_num
private theorem prime_sixtyTwoBH_137519 : Nat.Prime 137519 := by norm_num
private theorem prime_sixtyTwoBH_138077 : Nat.Prime 138077 := by norm_num
private theorem prime_sixtyTwoBH_148781 : Nat.Prime 148781 := by norm_num
private theorem prime_sixtyTwoBH_157393 : Nat.Prime 157393 := by norm_num
private theorem prime_sixtyTwoBH_160649 : Nat.Prime 160649 := by norm_num
private theorem prime_sixtyTwoBH_165703 : Nat.Prime 165703 := by norm_num
private theorem prime_sixtyTwoBH_176459 : Nat.Prime 176459 := by norm_num
private theorem prime_sixtyTwoBH_185051 : Nat.Prime 185051 := by norm_num
private theorem prime_sixtyTwoBH_186707 : Nat.Prime 186707 := by norm_num
private theorem prime_sixtyTwoBH_189361 : Nat.Prime 189361 := by norm_num
private theorem prime_sixtyTwoBH_223291 : Nat.Prime 223291 := by norm_num
private theorem prime_sixtyTwoBH_231017 : Nat.Prime 231017 := by norm_num
private theorem prime_sixtyTwoBH_233551 : Nat.Prime 233551 := by norm_num
private theorem prime_sixtyTwoBH_234083 : Nat.Prime 234083 := by norm_num
private theorem prime_sixtyTwoBH_237067 : Nat.Prime 237067 := by norm_num
private theorem prime_sixtyTwoBH_243031 : Nat.Prime 243031 := by norm_num
private theorem prime_sixtyTwoBH_285841 : Nat.Prime 285841 := by norm_num
private theorem prime_sixtyTwoBH_303649 : Nat.Prime 303649 := by norm_num
private theorem prime_sixtyTwoBH_319511 : Nat.Prime 319511 := by norm_num
private theorem prime_sixtyTwoBH_322039 : Nat.Prime 322039 := by norm_num
private theorem prime_sixtyTwoBH_325133 : Nat.Prime 325133 := by norm_num
private theorem prime_sixtyTwoBH_334991 : Nat.Prime 334991 := by norm_num
private theorem prime_sixtyTwoBH_351347 : Nat.Prime 351347 := by norm_num
private theorem prime_sixtyTwoBH_353699 : Nat.Prime 353699 := by norm_num
private theorem prime_sixtyTwoBH_392153 : Nat.Prime 392153 := by norm_num
private theorem prime_sixtyTwoBH_402343 : Nat.Prime 402343 := by norm_num
private theorem prime_sixtyTwoBH_406859 : Nat.Prime 406859 := by norm_num
private theorem prime_sixtyTwoBH_445853 : Nat.Prime 445853 := by norm_num
private theorem prime_sixtyTwoBH_458357 : Nat.Prime 458357 := by norm_num
private theorem prime_sixtyTwoBH_493121 : Nat.Prime 493121 := by norm_num
private theorem prime_sixtyTwoBH_540251 : Nat.Prime 540251 := by norm_num
private theorem prime_sixtyTwoBH_560653 : Nat.Prime 560653 := by norm_num
private theorem prime_sixtyTwoBH_580787 : Nat.Prime 580787 := by norm_num
private theorem prime_sixtyTwoBH_581491 : Nat.Prime 581491 := by norm_num
private theorem prime_sixtyTwoBH_593951 : Nat.Prime 593951 := by norm_num
private theorem prime_sixtyTwoBH_594929 : Nat.Prime 594929 := by norm_num
private theorem prime_sixtyTwoBH_617411 : Nat.Prime 617411 := by norm_num
private theorem prime_sixtyTwoBH_650873 : Nat.Prime 650873 := by norm_num
private theorem prime_sixtyTwoBH_681563 : Nat.Prime 681563 := by norm_num
private theorem prime_sixtyTwoBH_735983 : Nat.Prime 735983 := by norm_num
private theorem prime_sixtyTwoBH_753659 : Nat.Prime 753659 := by norm_num
private theorem prime_sixtyTwoBH_814031 : Nat.Prime 814031 := by norm_num
private theorem prime_sixtyTwoBH_839473 : Nat.Prime 839473 := by norm_num
private theorem prime_sixtyTwoBH_872479 : Nat.Prime 872479 := by norm_num
private theorem prime_sixtyTwoBH_883703 : Nat.Prime 883703 := by norm_num
private theorem prime_sixtyTwoBH_894233 : Nat.Prime 894233 := by norm_num
private theorem prime_sixtyTwoBH_902009 : Nat.Prime 902009 := by norm_num
private theorem prime_sixtyTwoBH_912559 : Nat.Prime 912559 := by norm_num
private theorem prime_sixtyTwoBH_928153 : Nat.Prime 928153 := by norm_num
private theorem prime_sixtyTwoBH_941701 : Nat.Prime 941701 := by norm_num
private theorem prime_sixtyTwoBH_1016621 : Nat.Prime 1016621 := by norm_num
private theorem prime_sixtyTwoBH_1020979 : Nat.Prime 1020979 := by norm_num
private theorem prime_sixtyTwoBH_1053497 : Nat.Prime 1053497 := by norm_num
private theorem prime_sixtyTwoBH_1137959 : Nat.Prime 1137959 := by norm_num
private theorem prime_sixtyTwoBH_1207259 : Nat.Prime 1207259 := by norm_num
private theorem prime_sixtyTwoBH_1292177 : Nat.Prime 1292177 := by norm_num
private theorem prime_sixtyTwoBH_1336949 : Nat.Prime 1336949 := by norm_num
private theorem prime_sixtyTwoBH_1431637 : Nat.Prime 1431637 := by norm_num
private theorem prime_sixtyTwoBH_1461407 : Nat.Prime 1461407 := by norm_num
private theorem prime_sixtyTwoBH_1545503 : Nat.Prime 1545503 := by norm_num
private theorem prime_sixtyTwoBH_1634603 : Nat.Prime 1634603 := by norm_num
private theorem prime_sixtyTwoBH_1653101 : Nat.Prime 1653101 := by norm_num
private theorem prime_sixtyTwoBH_1658509 : Nat.Prime 1658509 := by norm_num
private theorem prime_sixtyTwoBH_1803127 : Nat.Prime 1803127 := by norm_num
private theorem prime_sixtyTwoBH_1964617 : Nat.Prime 1964617 := by norm_num
private theorem prime_sixtyTwoBH_2092217 : Nat.Prime 2092217 := by norm_num
private theorem prime_sixtyTwoBH_2150867 : Nat.Prime 2150867 := by norm_num
private theorem prime_sixtyTwoBH_2180329 : Nat.Prime 2180329 := by norm_num
private theorem prime_sixtyTwoBH_2190901 : Nat.Prime 2190901 := by norm_num
private theorem prime_sixtyTwoBH_2237491 : Nat.Prime 2237491 := by norm_num
private theorem prime_sixtyTwoBH_2344141 : Nat.Prime 2344141 := by norm_num
private theorem prime_sixtyTwoBH_2453467 : Nat.Prime 2453467 := by norm_num
private theorem prime_sixtyTwoBH_2494507 : Nat.Prime 2494507 := by norm_num
private theorem prime_sixtyTwoBH_2653687 : Nat.Prime 2653687 := by norm_num
private theorem prime_sixtyTwoBH_2723779 : Nat.Prime 2723779 := by norm_num
private theorem prime_sixtyTwoBH_2726569 : Nat.Prime 2726569 := by norm_num
private theorem prime_sixtyTwoBH_2854261 : Nat.Prime 2854261 := by norm_num
private theorem prime_sixtyTwoBH_2882149 : Nat.Prime 2882149 := by norm_num
private theorem prime_sixtyTwoBH_3255773 : Nat.Prime 3255773 := by norm_num
private theorem prime_sixtyTwoBH_3332167 : Nat.Prime 3332167 := by norm_num
private theorem prime_sixtyTwoBH_3467693 : Nat.Prime 3467693 := by norm_num
private theorem prime_sixtyTwoBH_3653467 : Nat.Prime 3653467 := by norm_num
private theorem prime_sixtyTwoBH_4085827 : Nat.Prime 4085827 := by norm_num
private theorem prime_sixtyTwoBH_4237787 : Nat.Prime 4237787 := by norm_num
private theorem prime_sixtyTwoBH_4258829 : Nat.Prime 4258829 := by norm_num
private theorem prime_sixtyTwoBH_4575589 : Nat.Prime 4575589 := by norm_num
private theorem prime_sixtyTwoBH_4834777 : Nat.Prime 4834777 := by norm_num
private theorem prime_sixtyTwoBH_5328023 : Nat.Prime 5328023 := by norm_num
private theorem prime_sixtyTwoBH_5810201 : Nat.Prime 5810201 := by norm_num
private theorem prime_sixtyTwoBH_6069559 : Nat.Prime 6069559 := by norm_num
private theorem prime_sixtyTwoBH_6315527 : Nat.Prime 6315527 := by norm_num
private theorem prime_sixtyTwoBH_7001663 : Nat.Prime 7001663 := by norm_num
private theorem prime_sixtyTwoBH_7568959 : Nat.Prime 7568959 := by norm_num
private theorem prime_sixtyTwoBH_7742993 : Nat.Prime 7742993 := by norm_num
private theorem prime_sixtyTwoBH_7911539 : Nat.Prime 7911539 := by norm_num
private theorem prime_sixtyTwoBH_9618041 : Nat.Prime 9618041 := by norm_num
private theorem prime_sixtyTwoBH_10547107 : Nat.Prime 10547107 := by norm_num
private theorem prime_sixtyTwoBH_11164651 : Nat.Prime 11164651 := by norm_num
private theorem prime_sixtyTwoBH_11213303 : Nat.Prime 11213303 := by norm_num
private theorem prime_sixtyTwoBH_11756737 : Nat.Prime 11756737 := by norm_num
private theorem prime_sixtyTwoBH_12031991 : Nat.Prime 12031991 := by norm_num
private theorem prime_sixtyTwoBH_12212021 : Nat.Prime 12212021 := by norm_num
private theorem prime_sixtyTwoBH_12834911 : Nat.Prime 12834911 := by norm_num
private theorem prime_sixtyTwoBH_13328873 : Nat.Prime 13328873 := by norm_num
private theorem prime_sixtyTwoBH_13874867 : Nat.Prime 13874867 := by norm_num
private theorem prime_sixtyTwoBH_14602867 : Nat.Prime 14602867 := by norm_num
private theorem prime_sixtyTwoBH_15134731 : Nat.Prime 15134731 := by norm_num
private theorem prime_sixtyTwoBH_16580269 : Nat.Prime 16580269 := by norm_num
private theorem prime_sixtyTwoBH_17171603 : Nat.Prime 17171603 := by norm_num
private theorem prime_sixtyTwoBH_17577349 : Nat.Prime 17577349 := by norm_num
private theorem prime_sixtyTwoBH_18016421 : Nat.Prime 18016421 := by norm_num
private theorem prime_sixtyTwoBH_18386579 : Nat.Prime 18386579 := by norm_num
private theorem prime_sixtyTwoBH_19896319 : Nat.Prime 19896319 := by norm_num
private theorem prime_sixtyTwoBH_19917533 : Nat.Prime 19917533 := by norm_num
private theorem prime_sixtyTwoBH_22671373 : Nat.Prime 22671373 := by norm_num
private theorem prime_sixtyTwoBH_22833073 : Nat.Prime 22833073 := by norm_num
private theorem prime_sixtyTwoBH_23173441 : Nat.Prime 23173441 := by norm_num
private theorem prime_sixtyTwoBH_26146639 : Nat.Prime 26146639 := by norm_num
private theorem prime_sixtyTwoBH_27646081 : Nat.Prime 27646081 := by norm_num
private theorem prime_sixtyTwoBH_27789467 : Nat.Prime 27789467 := by norm_num
private theorem prime_sixtyTwoBH_27974981 : Nat.Prime 27974981 := by norm_num
private theorem prime_sixtyTwoBH_29743951 : Nat.Prime 29743951 := by norm_num
private theorem prime_sixtyTwoBH_31013497 : Nat.Prime 31013497 := by
  apply lucas_primality 31013497 (5 : ZMod 31013497)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (67, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (67, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 31013497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31013497) ^ 15506748 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31013497) ^ 10337832 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31013497) ^ 462888 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31013497) ^ 14472 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_31263041 : Nat.Prime 31263041 := by
  apply lucas_primality 31263041 (3 : ZMod 31263041)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (151, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (151, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 31263041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31263041) ^ 15631520 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 31263041) ^ 6252608 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 31263041) ^ 207040 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 31263041) ^ 48320 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_33520129 : Nat.Prime 33520129 := by
  apply lucas_primality 33520129 (7 : ZMod 33520129)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (139, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (139, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 33520129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_139
      · exact prime_sixtyTwoBH_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 33520129) ^ 16760064 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33520129) ^ 11173376 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33520129) ^ 241152 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33520129) ^ 213504 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_34359289 : Nat.Prime 34359289 := by
  apply lucas_primality 34359289 (7 : ZMod 34359289)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1431637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1431637, 1)] : List FactorBlock).map factorBlockValue).prod) = 34359289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1431637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34359289) ^ 17179644 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34359289) ^ 11453096 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34359289) ^ 24 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_36268619 : Nat.Prime 36268619 := by
  apply lucas_primality 36268619 (2 : ZMod 36268619)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (631, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (631, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) = 36268619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_631
      · exact prime_sixtyTwoBH_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36268619) ^ 18134309 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36268619) ^ 1250642 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36268619) ^ 57478 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36268619) ^ 36598 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_36388843 : Nat.Prime 36388843 := by
  apply lucas_primality 36388843 (2 : ZMod 36388843)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (293, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (293, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) = 36388843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_293
      · exact prime_sixtyTwoBH_2957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36388843) ^ 18194421 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36388843) ^ 12129614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36388843) ^ 5198406 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36388843) ^ 124194 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36388843) ^ 12306 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_36590497 : Nat.Prime 36590497 := by
  apply lucas_primality 36590497 (5 : ZMod 36590497)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (563, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (563, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 36590497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_563
      · exact prime_sixtyTwoBH_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36590497) ^ 18295248 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 36590497) ^ 12196832 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 36590497) ^ 64992 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 36590497) ^ 54048 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_42142567 : Nat.Prime 42142567 := by
  apply lucas_primality 42142567 (5 : ZMod 42142567)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1289, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1289, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) = 42142567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1289
      · exact prime_sixtyTwoBH_5449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42142567) ^ 21071283 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42142567) ^ 14047522 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42142567) ^ 32694 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42142567) ^ 7734 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_43781707 : Nat.Prime 43781707 := by
  apply lucas_primality 43781707 (3 : ZMod 43781707)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (83873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (83873, 1)] : List FactorBlock).map factorBlockValue).prod) = 43781707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_83873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 43781707) ^ 21890853 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 43781707) ^ 14593902 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 43781707) ^ 1509714 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 43781707) ^ 522 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_46594567 : Nat.Prime 46594567 := by
  apply lucas_primality 46594567 (3 : ZMod 46594567)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (269, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (269, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) = 46594567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_269
      · exact prime_sixtyTwoBH_9623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46594567) ^ 23297283 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46594567) ^ 15531522 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46594567) ^ 173214 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 46594567) ^ 4842 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_46966187 : Nat.Prime 46966187 := by
  apply lucas_primality 46966187 (2 : ZMod 46966187)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (863, 1), (27211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (863, 1), (27211, 1)] : List FactorBlock).map factorBlockValue).prod) = 46966187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_863
      · exact prime_sixtyTwoBH_27211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46966187) ^ 23483093 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46966187) ^ 54422 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46966187) ^ 1726 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_47026949 : Nat.Prime 47026949 := by
  apply lucas_primality 47026949 (2 : ZMod 47026949)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11756737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11756737, 1)] : List FactorBlock).map factorBlockValue).prod) = 47026949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11756737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 47026949) ^ 23513474 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47026949) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_55121959 : Nat.Prime 55121959 := by
  apply lucas_primality 55121959 (3 : ZMod 55121959)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (41, 1), (43, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (41, 1), (43, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 55121959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55121959) ^ 27560979 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55121959) ^ 18373986 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55121959) ^ 1344438 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55121959) ^ 1281906 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55121959) ^ 285606 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_69926561 : Nat.Prime 69926561 := by
  apply lucas_primality 69926561 (6 : ZMod 69926561)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (67, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (67, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 69926561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 69926561) ^ 34963280 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 69926561) ^ 13985312 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 69926561) ^ 6356960 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 69926561) ^ 1043680 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 69926561) ^ 117920 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_100592197 : Nat.Prime 100592197 := by
  apply lucas_primality 100592197 (5 : ZMod 100592197)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (37, 1), (13327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (37, 1), (13327, 1)] : List FactorBlock).map factorBlockValue).prod) = 100592197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_13327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100592197) ^ 50296098 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100592197) ^ 33530732 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100592197) ^ 5917188 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100592197) ^ 2718708 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100592197) ^ 7548 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_105461423 : Nat.Prime 105461423 := by
  apply lucas_primality 105461423 (5 : ZMod 105461423)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (263, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (263, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 105461423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_263
      · exact prime_sixtyTwoBH_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105461423) ^ 52730711 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 105461423) ^ 9587402 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 105461423) ^ 400994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 105461423) ^ 63646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_108577991 : Nat.Prime 108577991 := by
  apply lucas_primality 108577991 (11 : ZMod 108577991)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (231017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (231017, 1)] : List FactorBlock).map factorBlockValue).prod) = 108577991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_231017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 108577991) ^ 54288995 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 108577991) ^ 21715598 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 108577991) ^ 2310170 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 108577991) ^ 470 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_113611903 : Nat.Prime 113611903 := by
  apply lucas_primality 113611903 (3 : ZMod 113611903)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (421, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (421, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 113611903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_421
      · exact prime_sixtyTwoBH_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113611903) ^ 56805951 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113611903) ^ 37870634 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113611903) ^ 2771022 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113611903) ^ 269862 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113611903) ^ 103566 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_135960179 : Nat.Prime 135960179 := by
  apply lucas_primality 135960179 (2 : ZMod 135960179)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2344141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2344141, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_2344141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 135960179) ^ 67980089 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960179) ^ 4688282 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960179) ^ 58 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_136532827 : Nat.Prime 136532827 := by
  apply lucas_primality 136532827 (3 : ZMod 136532827)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (419, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (419, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 136532827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_419
      · exact prime_sixtyTwoBH_421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 136532827) ^ 68266413 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 136532827) ^ 45510942 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 136532827) ^ 3175182 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 136532827) ^ 325854 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 136532827) ^ 324306 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_139853123 : Nat.Prime 139853123 := by
  apply lucas_primality 139853123 (2 : ZMod 139853123)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (69926561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (69926561, 1)] : List FactorBlock).map factorBlockValue).prod) = 139853123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_69926561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 139853123) ^ 69926561 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139853123) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_144702529 : Nat.Prime 144702529 := by
  apply lucas_primality 144702529 (7 : ZMod 144702529)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (753659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (753659, 1)] : List FactorBlock).map factorBlockValue).prod) = 144702529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_753659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 144702529) ^ 72351264 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 144702529) ^ 48234176 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 144702529) ^ 192 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_156799711 : Nat.Prime 156799711 := by
  apply lucas_primality 156799711 (12 : ZMod 156799711)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (47087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (47087, 1)] : List FactorBlock).map factorBlockValue).prod) = 156799711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_47087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 156799711) ^ 78399855 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 156799711) ^ 52266570 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 156799711) ^ 31359942 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 156799711) ^ 4237830 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 156799711) ^ 3330 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_172343701 : Nat.Prime 172343701 := by
  apply lucas_primality 172343701 (6 : ZMod 172343701)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 2), (21277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 2), (21277, 1)] : List FactorBlock).map factorBlockValue).prod) = 172343701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_21277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 172343701) ^ 86171850 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 172343701) ^ 57447900 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 172343701) ^ 34468740 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 172343701) ^ 8100 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_193753997 : Nat.Prime 193753997 := by
  apply lucas_primality 193753997 (2 : ZMod 193753997)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (223, 1), (281, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (223, 1), (281, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 193753997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_223
      · exact prime_sixtyTwoBH_281
      · exact prime_sixtyTwoBH_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193753997) ^ 96876998 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 193753997) ^ 868852 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 193753997) ^ 689516 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 193753997) ^ 250652 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_194447167 : Nat.Prime 194447167 := by
  apply lucas_primality 194447167 (3 : ZMod 194447167)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (102233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (102233, 1)] : List FactorBlock).map factorBlockValue).prod) = 194447167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_317
      · exact prime_sixtyTwoBH_102233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 194447167) ^ 97223583 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194447167) ^ 64815722 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194447167) ^ 613398 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194447167) ^ 1902 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_195743809 : Nat.Prime 195743809 := by
  apply lucas_primality 195743809 (11 : ZMod 195743809)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (13, 1), (26141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (13, 1), (26141, 1)] : List FactorBlock).map factorBlockValue).prod) = 195743809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_26141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 195743809) ^ 97871904 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 195743809) ^ 65247936 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 195743809) ^ 15057216 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 195743809) ^ 7488 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_208040213 : Nat.Prime 208040213 := by
  apply lucas_primality 208040213 (2 : ZMod 208040213)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6373, 1), (8161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6373, 1), (8161, 1)] : List FactorBlock).map factorBlockValue).prod) = 208040213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_6373
      · exact prime_sixtyTwoBH_8161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 208040213) ^ 104020106 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 208040213) ^ 32644 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 208040213) ^ 25492 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_218917481 : Nat.Prime 218917481 := by
  apply lucas_primality 218917481 (3 : ZMod 218917481)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (83, 1), (233, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (83, 1), (233, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 218917481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_83
      · exact prime_sixtyTwoBH_233
      · exact prime_sixtyTwoBH_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 218917481) ^ 109458740 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 218917481) ^ 43783496 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 218917481) ^ 2637560 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 218917481) ^ 939560 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 218917481) ^ 773560 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_256351621 : Nat.Prime 256351621 := by
  apply lucas_primality 256351621 (13 : ZMod 256351621)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (269, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (269, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 256351621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_269
      · exact prime_sixtyTwoBH_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 256351621) ^ 128175810 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 256351621) ^ 85450540 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 256351621) ^ 51270324 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 256351621) ^ 36621660 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 256351621) ^ 952980 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 256351621) ^ 112980 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_260028833 : Nat.Prime 260028833 := by
  apply lucas_primality 260028833 (5 : ZMod 260028833)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (107, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (107, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 260028833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_107
      · exact prime_sixtyTwoBH_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 260028833) ^ 130014416 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 260028833) ^ 37146976 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 260028833) ^ 13685728 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 260028833) ^ 2430176 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 260028833) ^ 455392 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_262304363 : Nat.Prime 262304363 := by
  apply lucas_primality 262304363 (2 : ZMod 262304363)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (769, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (769, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 262304363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_769
      · exact prime_sixtyTwoBH_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 262304363) ^ 131152181 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 262304363) ^ 9044978 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 262304363) ^ 341098 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 262304363) ^ 44602 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_273445049 : Nat.Prime 273445049 := by
  apply lucas_primality 273445049 (3 : ZMod 273445049)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (571, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (571, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) = 273445049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_571
      · exact prime_sixtyTwoBH_1931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 273445049) ^ 136722524 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 273445049) ^ 8820808 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 273445049) ^ 478888 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 273445049) ^ 141608 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_275953003 : Nat.Prime 275953003 := by
  apply lucas_primality 275953003 (5 : ZMod 275953003)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (71, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (71, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 275953003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_71
      · exact prime_sixtyTwoBH_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 275953003) ^ 137976501 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 275953003) ^ 91984334 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 275953003) ^ 21227154 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 275953003) ^ 3886662 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 275953003) ^ 71994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_281797123 : Nat.Prime 281797123 := by
  apply lucas_primality 281797123 (2 : ZMod 281797123)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (46966187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (46966187, 1)] : List FactorBlock).map factorBlockValue).prod) = 281797123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_46966187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 281797123) ^ 140898561 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 281797123) ^ 93932374 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 281797123) ^ 6 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_285196117 : Nat.Prime 285196117 := by
  apply lucas_primality 285196117 (7 : ZMod 285196117)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (151, 1), (157393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (151, 1), (157393, 1)] : List FactorBlock).map factorBlockValue).prod) = 285196117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_157393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 285196117) ^ 142598058 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 285196117) ^ 95065372 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 285196117) ^ 1888716 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 285196117) ^ 1812 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_288725947 : Nat.Prime 288725947 := by
  apply lucas_primality 288725947 (3 : ZMod 288725947)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2092217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2092217, 1)] : List FactorBlock).map factorBlockValue).prod) = 288725947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_23
      · exact prime_sixtyTwoBH_2092217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 288725947) ^ 144362973 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288725947) ^ 96241982 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288725947) ^ 12553302 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288725947) ^ 138 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_309172987 : Nat.Prime 309172987 := by
  apply lucas_primality 309172987 (3 : ZMod 309172987)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (373, 1), (46049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (373, 1), (46049, 1)] : List FactorBlock).map factorBlockValue).prod) = 309172987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_373
      · exact prime_sixtyTwoBH_46049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 309172987) ^ 154586493 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 309172987) ^ 103057662 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 309172987) ^ 828882 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 309172987) ^ 6714 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_325205707 : Nat.Prime 325205707 := by
  apply lucas_primality 325205707 (2 : ZMod 325205707)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7742993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7742993, 1)] : List FactorBlock).map factorBlockValue).prod) = 325205707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_7742993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 325205707) ^ 162602853 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 325205707) ^ 108401902 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 325205707) ^ 46457958 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 325205707) ^ 42 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_334439461 : Nat.Prime 334439461 := by
  apply lucas_primality 334439461 (2 : ZMod 334439461)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (41, 1), (45317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (41, 1), (45317, 1)] : List FactorBlock).map factorBlockValue).prod) = 334439461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_45317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 334439461) ^ 167219730 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334439461) ^ 111479820 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334439461) ^ 66887892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334439461) ^ 8157060 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334439461) ^ 7380 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_363888431 : Nat.Prime 363888431 := by
  apply lucas_primality 363888431 (7 : ZMod 363888431)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (36388843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (36388843, 1)] : List FactorBlock).map factorBlockValue).prod) = 363888431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_36388843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 363888431) ^ 181944215 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 363888431) ^ 72777686 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 363888431) ^ 10 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_379695853 : Nat.Prime 379695853 := by
  apply lucas_primality 379695853 (2 : ZMod 379695853)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10547107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10547107, 1)] : List FactorBlock).map factorBlockValue).prod) = 379695853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_10547107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 379695853) ^ 189847926 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 379695853) ^ 126565284 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 379695853) ^ 36 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_397863569 : Nat.Prime 397863569 := by
  apply lucas_primality 397863569 (3 : ZMod 397863569)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (127, 1), (8513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (127, 1), (8513, 1)] : List FactorBlock).map factorBlockValue).prod) = 397863569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_23
      · exact prime_sixtyTwoBH_127
      · exact prime_sixtyTwoBH_8513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 397863569) ^ 198931784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 397863569) ^ 17298416 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 397863569) ^ 3132784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 397863569) ^ 46736 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_402368789 : Nat.Prime 402368789 := by
  apply lucas_primality 402368789 (2 : ZMod 402368789)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (100592197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (100592197, 1)] : List FactorBlock).map factorBlockValue).prod) = 402368789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_100592197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 402368789) ^ 201184394 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402368789) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_437834963 : Nat.Prime 437834963 := by
  apply lucas_primality 437834963 (2 : ZMod 437834963)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (218917481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (218917481, 1)] : List FactorBlock).map factorBlockValue).prod) = 437834963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_218917481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 437834963) ^ 218917481 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 437834963) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_490725667 : Nat.Prime 490725667 := by
  apply lucas_primality 490725667 (5 : ZMod 490725667)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2551, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2551, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 490725667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_2551
      · exact prime_sixtyTwoBH_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 490725667) ^ 245362833 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 490725667) ^ 163575222 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 490725667) ^ 192366 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 490725667) ^ 45918 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_494591501 : Nat.Prime 494591501 := by
  apply lucas_primality 494591501 (2 : ZMod 494591501)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (13, 1), (76091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (13, 1), (76091, 1)] : List FactorBlock).map factorBlockValue).prod) = 494591501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_76091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 494591501) ^ 247295750 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 494591501) ^ 98918300 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 494591501) ^ 38045500 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 494591501) ^ 6500 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_502327607 : Nat.Prime 502327607 := by
  apply lucas_primality 502327607 (5 : ZMod 502327607)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (22833073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (22833073, 1)] : List FactorBlock).map factorBlockValue).prod) = 502327607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_22833073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 502327607) ^ 251163803 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 502327607) ^ 45666146 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 502327607) ^ 22 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_549491297 : Nat.Prime 549491297 := by
  apply lucas_primality 549491297 (3 : ZMod 549491297)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17171603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17171603, 1)] : List FactorBlock).map factorBlockValue).prod) = 549491297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_17171603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 549491297) ^ 274745648 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 549491297) ^ 32 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_554424461 : Nat.Prime 554424461 := by
  apply lucas_primality 554424461 (2 : ZMod 554424461)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (894233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (894233, 1)] : List FactorBlock).map factorBlockValue).prod) = 554424461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_894233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 554424461) ^ 277212230 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 554424461) ^ 110884892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 554424461) ^ 17884660 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 554424461) ^ 620 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_574016063 : Nat.Prime 574016063 := by
  apply lucas_primality 574016063 (5 : ZMod 574016063)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (2190901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (2190901, 1)] : List FactorBlock).map factorBlockValue).prod) = 574016063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_131
      · exact prime_sixtyTwoBH_2190901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 574016063) ^ 287008031 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 574016063) ^ 4381802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 574016063) ^ 262 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_606864239 : Nat.Prime 606864239 := by
  apply lucas_primality 606864239 (7 : ZMod 606864239)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6367, 1), (47657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6367, 1), (47657, 1)] : List FactorBlock).map factorBlockValue).prod) = 606864239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_6367
      · exact prime_sixtyTwoBH_47657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 606864239) ^ 303432119 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 606864239) ^ 95314 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 606864239) ^ 12734 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_645618223 : Nat.Prime 645618223 := by
  apply lucas_primality 645618223 (5 : ZMod 645618223)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (211, 1), (56663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (211, 1), (56663, 1)] : List FactorBlock).map factorBlockValue).prod) = 645618223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_211
      · exact prime_sixtyTwoBH_56663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 645618223) ^ 322809111 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 645618223) ^ 215206074 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 645618223) ^ 3059802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 645618223) ^ 11394 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_781123943 : Nat.Prime 781123943 := by
  apply lucas_primality 781123943 (5 : ZMod 781123943)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2357, 1), (165703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2357, 1), (165703, 1)] : List FactorBlock).map factorBlockValue).prod) = 781123943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_2357
      · exact prime_sixtyTwoBH_165703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 781123943) ^ 390561971 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 781123943) ^ 331406 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 781123943) ^ 4714 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_799162913 : Nat.Prime 799162913 := by
  apply lucas_primality 799162913 (3 : ZMod 799162913)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (43, 1), (580787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (43, 1), (580787, 1)] : List FactorBlock).map factorBlockValue).prod) = 799162913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_580787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 799162913) ^ 399581456 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 799162913) ^ 18585184 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 799162913) ^ 1376 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_807835181 : Nat.Prime 807835181 := by
  apply lucas_primality 807835181 (2 : ZMod 807835181)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (392153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (392153, 1)] : List FactorBlock).map factorBlockValue).prod) = 807835181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_103
      · exact prime_sixtyTwoBH_392153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 807835181) ^ 403917590 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 807835181) ^ 161567036 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 807835181) ^ 7843060 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 807835181) ^ 2060 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_815175941 : Nat.Prime 815175941 := by
  apply lucas_primality 815175941 (2 : ZMod 815175941)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (43, 1), (61, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (43, 1), (61, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 815175941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 815175941) ^ 407587970 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 815175941) ^ 163035188 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 815175941) ^ 19882340 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 815175941) ^ 18957580 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 815175941) ^ 13363540 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 815175941) ^ 2150860 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_816891451 : Nat.Prime 816891451 := by
  apply lucas_primality 816891451 (2 : ZMod 816891451)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (331, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (331, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) = 816891451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_331
      · exact prime_sixtyTwoBH_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 816891451) ^ 408445725 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 816891451) ^ 272297150 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 816891451) ^ 163378290 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 816891451) ^ 2467950 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 816891451) ^ 49650 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_939845209 : Nat.Prime 939845209 := by
  apply lucas_primality 939845209 (22 : ZMod 939845209)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (137, 1), (285841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (137, 1), (285841, 1)] : List FactorBlock).map factorBlockValue).prod) = 939845209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_137
      · exact prime_sixtyTwoBH_285841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 939845209) ^ 469922604 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 939845209) ^ 313281736 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 939845209) ^ 6860184 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 939845209) ^ 3288 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_940798267 : Nat.Prime 940798267 := by
  apply lucas_primality 940798267 (5 : ZMod 940798267)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (156799711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (156799711, 1)] : List FactorBlock).map factorBlockValue).prod) = 940798267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_156799711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 940798267) ^ 470399133 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 940798267) ^ 313599422 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 940798267) ^ 6 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1121063921 : Nat.Prime 1121063921 := by
  apply lucas_primality 1121063921 (3 : ZMod 1121063921)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (73, 1), (97, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (73, 1), (97, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121063921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_97
      · exact prime_sixtyTwoBH_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1121063921) ^ 560531960 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1121063921) ^ 224212784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1121063921) ^ 15357040 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1121063921) ^ 11557360 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1121063921) ^ 566480 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1175916793 : Nat.Prime 1175916793 := by
  apply lucas_primality 1175916793 (5 : ZMod 1175916793)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (2882149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (2882149, 1)] : List FactorBlock).map factorBlockValue).prod) = 1175916793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_2882149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1175916793) ^ 587958396 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1175916793) ^ 391972264 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1175916793) ^ 69171576 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1175916793) ^ 408 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1189758041 : Nat.Prime 1189758041 := by
  apply lucas_primality 1189758041 (3 : ZMod 1189758041)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29743951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29743951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1189758041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_29743951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1189758041) ^ 594879020 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189758041) ^ 237951608 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1189758041) ^ 40 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1371678331 : Nat.Prime 1371678331 := by
  apply lucas_primality 1371678331 (2 : ZMod 1371678331)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (68141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (68141, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371678331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_68141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1371678331) ^ 685839165 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371678331) ^ 457226110 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371678331) ^ 274335666 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371678331) ^ 124698030 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371678331) ^ 22486530 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1371678331) ^ 20130 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1545167339 : Nat.Prime 1545167339 := by
  apply lucas_primality 1545167339 (2 : ZMod 1545167339)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (13, 2), (37781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (13, 2), (37781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1545167339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_37781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1545167339) ^ 772583669 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1545167339) ^ 140469758 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1545167339) ^ 118859026 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1545167339) ^ 40898 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1556225087 : Nat.Prime 1556225087 := by
  apply lucas_primality 1556225087 (5 : ZMod 1556225087)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 2), (71171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1556225087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_71171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1556225087) ^ 778112543 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1556225087) ^ 119709622 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1556225087) ^ 53662934 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1556225087) ^ 21866 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1618355021 : Nat.Prime 1618355021 := by
  apply lucas_primality 1618355021 (2 : ZMod 1618355021)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (4258829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (4258829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1618355021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_4258829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1618355021) ^ 809177510 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618355021) ^ 323671004 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618355021) ^ 85176580 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618355021) ^ 380 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1630351883 : Nat.Prime 1630351883 := by
  apply lucas_primality 1630351883 (2 : ZMod 1630351883)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (815175941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (815175941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630351883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_815175941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1630351883) ^ 815175941 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630351883) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1631522149 : Nat.Prime 1631522149 := by
  apply lucas_primality 1631522149 (7 : ZMod 1631522149)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (135960179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (135960179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631522149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_135960179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1631522149) ^ 815761074 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1631522149) ^ 543840716 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1631522149) ^ 12 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1649002021 : Nat.Prime 1649002021 := by
  apply lucas_primality 1649002021 (2 : ZMod 1649002021)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (61, 1), (1031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (61, 1), (1031, 1)] : List FactorBlock).map factorBlockValue).prod) = 1649002021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_23
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_1031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1649002021) ^ 824501010 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 549667340 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 329800404 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 86789580 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 71695740 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 27032820 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1649002021) ^ 1599420 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1818859561 : Nat.Prime 1818859561 := by
  apply lucas_primality 1818859561 (23 : ZMod 1818859561)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (277, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (277, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1818859561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_277
      · exact prime_sixtyTwoBH_7817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1818859561) ^ 909429780 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (23 : ZMod 1818859561) ^ 606286520 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (23 : ZMod 1818859561) ^ 363771912 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (23 : ZMod 1818859561) ^ 259837080 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (23 : ZMod 1818859561) ^ 6566280 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (23 : ZMod 1818859561) ^ 232680 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2242127843 : Nat.Prime 2242127843 := by
  apply lucas_primality 2242127843 (2 : ZMod 2242127843)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1121063921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1121063921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242127843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_1121063921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2242127843) ^ 1121063921 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2242127843) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2469700643 : Nat.Prime 2469700643 := by
  apply lucas_primality 2469700643 (2 : ZMod 2469700643)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 2), (902009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 2), (902009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2469700643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_902009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2469700643) ^ 1234850321 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2469700643) ^ 66748666 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2469700643) ^ 2738 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2599310327 : Nat.Prime 2599310327 := by
  apply lucas_primality 2599310327 (5 : ZMod 2599310327)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (14602867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (14602867, 1)] : List FactorBlock).map factorBlockValue).prod) = 2599310327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_89
      · exact prime_sixtyTwoBH_14602867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2599310327) ^ 1299655163 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2599310327) ^ 29205734 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2599310327) ^ 178 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2703369671 : Nat.Prime 2703369671 := by
  apply lucas_primality 2703369671 (7 : ZMod 2703369671)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (1658509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (1658509, 1)] : List FactorBlock).map factorBlockValue).prod) = 2703369671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_163
      · exact prime_sixtyTwoBH_1658509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2703369671) ^ 1351684835 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2703369671) ^ 540673934 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2703369671) ^ 16585090 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2703369671) ^ 1630 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2776559479 : Nat.Prime 2776559479 := by
  apply lucas_primality 2776559479 (3 : ZMod 2776559479)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (107, 1), (56167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (107, 1), (56167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2776559479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_107
      · exact prime_sixtyTwoBH_56167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2776559479) ^ 1388279739 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776559479) ^ 925519826 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776559479) ^ 396651354 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776559479) ^ 252414498 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776559479) ^ 25949154 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776559479) ^ 49434 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2982708439 : Nat.Prime 2982708439 := by
  apply lucas_primality 2982708439 (3 : ZMod 2982708439)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (7001663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (7001663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2982708439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_71
      · exact prime_sixtyTwoBH_7001663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2982708439) ^ 1491354219 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2982708439) ^ 994236146 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2982708439) ^ 42009978 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2982708439) ^ 426 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3120345997 : Nat.Prime 3120345997 := by
  apply lucas_primality 3120345997 (2 : ZMod 3120345997)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (260028833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (260028833, 1)] : List FactorBlock).map factorBlockValue).prod) = 3120345997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_260028833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3120345997) ^ 1560172998 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3120345997) ^ 1040115332 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3120345997) ^ 12 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3183772061 : Nat.Prime 3183772061 := by
  apply lucas_primality 3183772061 (2 : ZMod 3183772061)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (71, 1), (45757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (71, 1), (45757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3183772061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_71
      · exact prime_sixtyTwoBH_45757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3183772061) ^ 1591886030 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183772061) ^ 636754412 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183772061) ^ 454824580 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183772061) ^ 44841860 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3183772061) ^ 69580 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3237811001 : Nat.Prime 3237811001 := by
  apply lucas_primality 3237811001 (3 : ZMod 3237811001)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (41, 1), (157, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (41, 1), (157, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 3237811001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_157
      · exact prime_sixtyTwoBH_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3237811001) ^ 1618905500 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3237811001) ^ 647562200 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3237811001) ^ 78971000 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3237811001) ^ 20623000 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3237811001) ^ 6437000 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3375149293 : Nat.Prime 3375149293 := by
  apply lucas_primality 3375149293 (2 : ZMod 3375149293)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43, 1), (2180329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43, 1), (2180329, 1)] : List FactorBlock).map factorBlockValue).prod) = 3375149293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_2180329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3375149293) ^ 1687574646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3375149293) ^ 1125049764 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3375149293) ^ 78491844 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3375149293) ^ 1548 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3848253449 : Nat.Prime 3848253449 := by
  apply lucas_primality 3848253449 (6 : ZMod 3848253449)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (31, 1), (211, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (31, 1), (211, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3848253449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_211
      · exact prime_sixtyTwoBH_5657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3848253449) ^ 1924126724 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3848253449) ^ 296019496 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3848253449) ^ 124137208 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3848253449) ^ 18238168 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3848253449) ^ 680264 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4028852459 : Nat.Prime 4028852459 := by
  apply lucas_primality 4028852459 (2 : ZMod 4028852459)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3593, 1), (560653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3593, 1), (560653, 1)] : List FactorBlock).map factorBlockValue).prod) = 4028852459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3593
      · exact prime_sixtyTwoBH_560653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4028852459) ^ 2014426229 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4028852459) ^ 1121306 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4028852459) ^ 7186 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4484255687 : Nat.Prime 4484255687 := by
  apply lucas_primality 4484255687 (5 : ZMod 4484255687)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2242127843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2242127843, 1)] : List FactorBlock).map factorBlockValue).prod) = 4484255687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_2242127843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4484255687) ^ 2242127843 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4484255687) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4589997557 : Nat.Prime 4589997557 := by
  apply lucas_primality 4589997557 (2 : ZMod 4589997557)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (31013497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (31013497, 1)] : List FactorBlock).map factorBlockValue).prod) = 4589997557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_31013497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4589997557) ^ 2294998778 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4589997557) ^ 124053988 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4589997557) ^ 148 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4615091137 : Nat.Prime 4615091137 := by
  apply lucas_primality 4615091137 (7 : ZMod 4615091137)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (2203, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (2203, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) = 4615091137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_2203
      · exact prime_sixtyTwoBH_3637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4615091137) ^ 2307545568 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4615091137) ^ 1538363712 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4615091137) ^ 2094912 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4615091137) ^ 1268928 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4942227799 : Nat.Prime 4942227799 := by
  apply lucas_primality 4942227799 (3 : ZMod 4942227799)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (67, 1), (50593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (67, 1), (50593, 1)] : List FactorBlock).map factorBlockValue).prod) = 4942227799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_50593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4942227799) ^ 2471113899 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4942227799) ^ 1647409266 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4942227799) ^ 73764594 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4942227799) ^ 97686 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6301611167 : Nat.Prime 6301611167 := by
  apply lucas_primality 6301611167 (5 : ZMod 6301611167)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (47026949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (47026949, 1)] : List FactorBlock).map factorBlockValue).prod) = 6301611167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_47026949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6301611167) ^ 3150805583 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6301611167) ^ 94053898 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6301611167) ^ 134 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6475622003 : Nat.Prime 6475622003 := by
  apply lucas_primality 6475622003 (2 : ZMod 6475622003)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3237811001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3237811001, 1)] : List FactorBlock).map factorBlockValue).prod) = 6475622003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3237811001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6475622003) ^ 3237811001 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6475622003) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6625628957 : Nat.Prime 6625628957 := by
  apply lucas_primality 6625628957 (3 : ZMod 6625628957)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (421, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (421, 1), (135671, 1)] : List FactorBlock).map factorBlockValue).prod) = 6625628957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_421
      · exact prime_sixtyTwoBH_135671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6625628957) ^ 3312814478 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6625628957) ^ 228469964 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6625628957) ^ 15737836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6625628957) ^ 48836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_7157318353 : Nat.Prime 7157318353 := by
  apply lucas_primality 7157318353 (5 : ZMod 7157318353)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (3467693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (3467693, 1)] : List FactorBlock).map factorBlockValue).prod) = 7157318353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_3467693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7157318353) ^ 3578659176 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7157318353) ^ 2385772784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7157318353) ^ 166449264 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7157318353) ^ 2064 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_7996883617 : Nat.Prime 7996883617 := by
  apply lucas_primality 7996883617 (5 : ZMod 7996883617)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (23, 1), (1207259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (23, 1), (1207259, 1)] : List FactorBlock).map factorBlockValue).prod) = 7996883617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_23
      · exact prime_sixtyTwoBH_1207259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7996883617) ^ 3998441808 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7996883617) ^ 2665627872 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7996883617) ^ 347690592 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7996883617) ^ 6624 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_8154169129 : Nat.Prime 8154169129 := by
  apply lucas_primality 8154169129 (22 : ZMod 8154169129)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (1447, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (1447, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) = 8154169129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_1447
      · exact prime_sixtyTwoBH_3727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 8154169129) ^ 4077084564 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 8154169129) ^ 2718056376 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 8154169129) ^ 1164881304 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 8154169129) ^ 5635224 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (22 : ZMod 8154169129) ^ 2187864 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_8215814953 : Nat.Prime 8215814953 := by
  apply lucas_primality 8215814953 (5 : ZMod 8215814953)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (43, 1), (2653687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (43, 1), (2653687, 1)] : List FactorBlock).map factorBlockValue).prod) = 8215814953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_2653687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8215814953) ^ 4107907476 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 8215814953) ^ 2738604984 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 8215814953) ^ 191065464 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 8215814953) ^ 3096 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9380721067 : Nat.Prime 9380721067 := by
  apply lucas_primality 9380721067 (3 : ZMod 9380721067)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11369, 1), (137519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11369, 1), (137519, 1)] : List FactorBlock).map factorBlockValue).prod) = 9380721067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11369
      · exact prime_sixtyTwoBH_137519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9380721067) ^ 4690360533 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9380721067) ^ 3126907022 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9380721067) ^ 825114 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9380721067) ^ 68214 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9710130127 : Nat.Prime 9710130127 := by
  apply lucas_primality 9710130127 (3 : ZMod 9710130127)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1618355021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1618355021, 1)] : List FactorBlock).map factorBlockValue).prod) = 9710130127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1618355021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9710130127) ^ 4855065063 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9710130127) ^ 3236710042 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9710130127) ^ 6 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9738555329 : Nat.Prime 9738555329 := by
  apply lucas_primality 9738555329 (6 : ZMod 9738555329)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (61, 1), (2494507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (61, 1), (2494507, 1)] : List FactorBlock).map factorBlockValue).prod) = 9738555329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_2494507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 9738555329) ^ 4869277664 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9738555329) ^ 159648448 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9738555329) ^ 3904 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_10143362147 : Nat.Prime 10143362147 := by
  apply lucas_primality 10143362147 (2 : ZMod 10143362147)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1049, 1), (4834777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1049, 1), (4834777, 1)] : List FactorBlock).map factorBlockValue).prod) = 10143362147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_1049
      · exact prime_sixtyTwoBH_4834777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10143362147) ^ 5071681073 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143362147) ^ 9669554 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10143362147) ^ 2098 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_12763458317 : Nat.Prime 12763458317 := by
  apply lucas_primality 12763458317 (2 : ZMod 12763458317)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (43, 1), (89, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (43, 1), (89, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 12763458317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_89
      · exact prime_sixtyTwoBH_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12763458317) ^ 6381729158 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12763458317) ^ 1823351188 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12763458317) ^ 671760964 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12763458317) ^ 296824612 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12763458317) ^ 143409644 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12763458317) ^ 2035964 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_17445792599 : Nat.Prime 17445792599 := by
  apply lucas_primality 17445792599 (7 : ZMod 17445792599)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 3), (17, 1), (233551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 3), (17, 1), (233551, 1)] : List FactorBlock).map factorBlockValue).prod) = 17445792599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_233551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17445792599) ^ 8722896299 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 17445792599) ^ 1341984046 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 17445792599) ^ 1026223094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 17445792599) ^ 74698 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_22122940289 : Nat.Prime 22122940289 := by
  apply lucas_primality 22122940289 (3 : ZMod 22122940289)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11701, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11701, 1), (14771, 1)] : List FactorBlock).map factorBlockValue).prod) = 22122940289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11701
      · exact prime_sixtyTwoBH_14771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22122940289) ^ 11061470144 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 22122940289) ^ 1890688 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 22122940289) ^ 1497728 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_25539476939 : Nat.Prime 25539476939 := by
  apply lucas_primality 25539476939 (2 : ZMod 25539476939)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1181, 1), (1459, 1), (7411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1181, 1), (1459, 1), (7411, 1)] : List FactorBlock).map factorBlockValue).prod) = 25539476939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_1181
      · exact prime_sixtyTwoBH_1459
      · exact prime_sixtyTwoBH_7411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25539476939) ^ 12769738469 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 25539476939) ^ 21625298 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 25539476939) ^ 17504782 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 25539476939) ^ 3446158 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_30951171989 : Nat.Prime 30951171989 := by
  apply lucas_primality 30951171989 (2 : ZMod 30951171989)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (3463, 1), (10691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (3463, 1), (10691, 1)] : List FactorBlock).map factorBlockValue).prod) = 30951171989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_3463
      · exact prime_sixtyTwoBH_10691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30951171989) ^ 15475585994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30951171989) ^ 2813742908 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30951171989) ^ 1629009052 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30951171989) ^ 8937676 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30951171989) ^ 2895068 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_35965406761 : Nat.Prime 35965406761 := by
  apply lucas_primality 35965406761 (17 : ZMod 35965406761)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (29, 1), (2503, 1), (4129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (29, 1), (2503, 1), (4129, 1)] : List FactorBlock).map factorBlockValue).prod) = 35965406761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_2503
      · exact prime_sixtyTwoBH_4129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 35965406761) ^ 17982703380 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 35965406761) ^ 11988468920 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 35965406761) ^ 7193081352 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 35965406761) ^ 1240186440 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 35965406761) ^ 14368920 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 35965406761) ^ 8710440 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_37073450599 : Nat.Prime 37073450599 := by
  apply lucas_primality 37073450599 (3 : ZMod 37073450599)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (325205707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (325205707, 1)] : List FactorBlock).map factorBlockValue).prod) = 37073450599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_325205707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37073450599) ^ 18536725299 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 37073450599) ^ 12357816866 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 37073450599) ^ 1951234242 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 37073450599) ^ 114 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_41005828973 : Nat.Prime 41005828973 := by
  apply lucas_primality 41005828973 (2 : ZMod 41005828973)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (68903, 1), (148781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (68903, 1), (148781, 1)] : List FactorBlock).map factorBlockValue).prod) = 41005828973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_68903
      · exact prime_sixtyTwoBH_148781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41005828973) ^ 20502914486 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 41005828973) ^ 595124 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 41005828973) ^ 275612 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_53542646173 : Nat.Prime 53542646173 := by
  apply lucas_primality 53542646173 (5 : ZMod 53542646173)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1151, 1), (1292177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1151, 1), (1292177, 1)] : List FactorBlock).map factorBlockValue).prod) = 53542646173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1151
      · exact prime_sixtyTwoBH_1292177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53542646173) ^ 26771323086 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 53542646173) ^ 17847548724 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 53542646173) ^ 46518372 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 53542646173) ^ 41436 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_58199031427 : Nat.Prime 58199031427 := by
  apply lucas_primality 58199031427 (2 : ZMod 58199031427)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (19917533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (19917533, 1)] : List FactorBlock).map factorBlockValue).prod) = 58199031427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_487
      · exact prime_sixtyTwoBH_19917533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58199031427) ^ 29099515713 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 58199031427) ^ 19399677142 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 58199031427) ^ 119505198 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 58199031427) ^ 2922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_69343275643 : Nat.Prime 69343275643 := by
  apply lucas_primality 69343275643 (3 : ZMod 69343275643)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (709, 1), (124433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (709, 1), (124433, 1)] : List FactorBlock).map factorBlockValue).prod) = 69343275643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_131
      · exact prime_sixtyTwoBH_709
      · exact prime_sixtyTwoBH_124433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69343275643) ^ 34671637821 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 69343275643) ^ 23114425214 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 69343275643) ^ 529337982 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 69343275643) ^ 97804338 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 69343275643) ^ 557274 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_79528332101 : Nat.Prime 79528332101 := by
  apply lucas_primality 79528332101 (3 : ZMod 79528332101)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (113611903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (113611903, 1)] : List FactorBlock).map factorBlockValue).prod) = 79528332101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_113611903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 79528332101) ^ 39764166050 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 79528332101) ^ 15905666420 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 79528332101) ^ 11361190300 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 79528332101) ^ 700 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_87018551603 : Nat.Prime 87018551603 := by
  apply lucas_primality 87018551603 (2 : ZMod 87018551603)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (257, 1), (4575589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (257, 1), (4575589, 1)] : List FactorBlock).map factorBlockValue).prod) = 87018551603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_257
      · exact prime_sixtyTwoBH_4575589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87018551603) ^ 43509275801 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87018551603) ^ 2351852746 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87018551603) ^ 338593586 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87018551603) ^ 19018 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_89264625547 : Nat.Prime 89264625547 := by
  apply lucas_primality 89264625547 (3 : ZMod 89264625547)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (569, 1), (26146639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (569, 1), (26146639, 1)] : List FactorBlock).map factorBlockValue).prod) = 89264625547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_569
      · exact prime_sixtyTwoBH_26146639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89264625547) ^ 44632312773 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89264625547) ^ 29754875182 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89264625547) ^ 156879834 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89264625547) ^ 3414 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_103954491923 : Nat.Prime 103954491923 := by
  apply lucas_primality 103954491923 (2 : ZMod 103954491923)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (87511, 1), (593951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (87511, 1), (593951, 1)] : List FactorBlock).map factorBlockValue).prod) = 103954491923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_87511
      · exact prime_sixtyTwoBH_593951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103954491923) ^ 51977245961 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 103954491923) ^ 1187902 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 103954491923) ^ 175022 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_112601491447 : Nat.Prime 112601491447 := by
  apply lucas_primality 112601491447 (3 : ZMod 112601491447)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (547, 1), (353699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (547, 1), (353699, 1)] : List FactorBlock).map factorBlockValue).prod) = 112601491447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_97
      · exact prime_sixtyTwoBH_547
      · exact prime_sixtyTwoBH_353699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112601491447) ^ 56300745723 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 112601491447) ^ 37533830482 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 112601491447) ^ 1160840118 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 112601491447) ^ 205852818 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 112601491447) ^ 318354 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_113990945639 : Nat.Prime 113990945639 := by
  apply lucas_primality 113990945639 (7 : ZMod 113990945639)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (479, 1), (1336949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (479, 1), (1336949, 1)] : List FactorBlock).map factorBlockValue).prod) = 113990945639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_89
      · exact prime_sixtyTwoBH_479
      · exact prime_sixtyTwoBH_1336949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 113990945639) ^ 56995472819 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 113990945639) ^ 1280797142 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 113990945639) ^ 237976922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 113990945639) ^ 85262 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_120443904577 : Nat.Prime 120443904577 := by
  apply lucas_primality 120443904577 (10 : ZMod 120443904577)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (107, 1), (227, 1), (8609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (107, 1), (227, 1), (8609, 1)] : List FactorBlock).map factorBlockValue).prod) = 120443904577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_107
      · exact prime_sixtyTwoBH_227
      · exact prime_sixtyTwoBH_8609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 120443904577) ^ 60221952288 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 120443904577) ^ 40147968192 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 120443904577) ^ 1125643968 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 120443904577) ^ 530589888 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 120443904577) ^ 13990464 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_130527382327 : Nat.Prime 130527382327 := by
  apply lucas_primality 130527382327 (3 : ZMod 130527382327)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (33520129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (33520129, 1)] : List FactorBlock).map factorBlockValue).prod) = 130527382327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_59
      · exact prime_sixtyTwoBH_33520129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130527382327) ^ 65263691163 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130527382327) ^ 43509127442 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130527382327) ^ 11866125666 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130527382327) ^ 2212328514 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130527382327) ^ 3894 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_133171645003 : Nat.Prime 133171645003 := by
  apply lucas_primality 133171645003 (2 : ZMod 133171645003)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (89, 1), (22671373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (89, 1), (22671373, 1)] : List FactorBlock).map factorBlockValue).prod) = 133171645003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_89
      · exact prime_sixtyTwoBH_22671373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133171645003) ^ 66585822501 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 133171645003) ^ 44390548334 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 133171645003) ^ 12106513182 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 133171645003) ^ 1496310618 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 133171645003) ^ 5874 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_185577411377 : Nat.Prime 185577411377 := by
  apply lucas_primality 185577411377 (3 : ZMod 185577411377)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (53, 1), (31263041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (53, 1), (31263041, 1)] : List FactorBlock).map factorBlockValue).prod) = 185577411377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_53
      · exact prime_sixtyTwoBH_31263041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 185577411377) ^ 92788705688 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185577411377) ^ 26511058768 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185577411377) ^ 3501460592 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185577411377) ^ 5936 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_196309007729 : Nat.Prime 196309007729 := by
  apply lucas_primality 196309007729 (3 : ZMod 196309007729)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113, 1), (108577991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113, 1), (108577991, 1)] : List FactorBlock).map factorBlockValue).prod) = 196309007729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_113
      · exact prime_sixtyTwoBH_108577991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 196309007729) ^ 98154503864 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 196309007729) ^ 1737247856 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 196309007729) ^ 1808 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_201776001689 : Nat.Prime 201776001689 := by
  apply lucas_primality 201776001689 (3 : ZMod 201776001689)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (1759, 1), (243031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (1759, 1), (243031, 1)] : List FactorBlock).map factorBlockValue).prod) = 201776001689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_59
      · exact prime_sixtyTwoBH_1759
      · exact prime_sixtyTwoBH_243031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 201776001689) ^ 100888000844 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 201776001689) ^ 3419932232 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 201776001689) ^ 114710632 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 201776001689) ^ 830248 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_251038026307 : Nat.Prime 251038026307 := by
  apply lucas_primality 251038026307 (2 : ZMod 251038026307)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1097, 1), (4237787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1097, 1), (4237787, 1)] : List FactorBlock).map factorBlockValue).prod) = 251038026307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1097
      · exact prime_sixtyTwoBH_4237787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 251038026307) ^ 125519013153 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 251038026307) ^ 83679342102 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 251038026307) ^ 228840498 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 251038026307) ^ 59238 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_282906338573 : Nat.Prime 282906338573 := by
  apply lucas_primality 282906338573 (2 : ZMod 282906338573)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (494591501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (494591501, 1)] : List FactorBlock).map factorBlockValue).prod) = 282906338573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_494591501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 282906338573) ^ 141453169286 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 282906338573) ^ 25718758052 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 282906338573) ^ 21762026044 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 282906338573) ^ 572 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_286623877369 : Nat.Prime 286623877369 := by
  apply lucas_primality 286623877369 (13 : ZMod 286623877369)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (61, 1), (6315527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (61, 1), (6315527, 1)] : List FactorBlock).map factorBlockValue).prod) = 286623877369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_6315527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 286623877369) ^ 143311938684 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 286623877369) ^ 95541292456 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 286623877369) ^ 9245931528 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 286623877369) ^ 4698752088 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 286623877369) ^ 45384 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_289182573529 : Nat.Prime 289182573529 := by
  apply lucas_primality 289182573529 (7 : ZMod 289182573529)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1523, 1), (7911539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1523, 1), (7911539, 1)] : List FactorBlock).map factorBlockValue).prod) = 289182573529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1523
      · exact prime_sixtyTwoBH_7911539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 289182573529) ^ 144591286764 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 289182573529) ^ 96394191176 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 289182573529) ^ 189876936 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 289182573529) ^ 36552 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_301345198709 : Nat.Prime 301345198709 := by
  apply lucas_primality 301345198709 (2 : ZMod 301345198709)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (239, 1), (277, 1), (1137959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (239, 1), (277, 1), (1137959, 1)] : List FactorBlock).map factorBlockValue).prod) = 301345198709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_239
      · exact prime_sixtyTwoBH_277
      · exact prime_sixtyTwoBH_1137959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 301345198709) ^ 150672599354 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 301345198709) ^ 1260858572 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 301345198709) ^ 1087888804 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 301345198709) ^ 264812 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_394488991319 : Nat.Prime 394488991319 := by
  apply lucas_primality 394488991319 (11 : ZMod 394488991319)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1289, 1), (3255773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1289, 1), (3255773, 1)] : List FactorBlock).map factorBlockValue).prod) = 394488991319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_1289
      · exact prime_sixtyTwoBH_3255773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 394488991319) ^ 197244495659 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 394488991319) ^ 8393382794 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 394488991319) ^ 306042662 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 394488991319) ^ 121166 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_535341429929 : Nat.Prime 535341429929 := by
  apply lucas_primality 535341429929 (3 : ZMod 535341429929)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (1556225087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (1556225087, 1)] : List FactorBlock).map factorBlockValue).prod) = 535341429929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_1556225087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 535341429929) ^ 267670714964 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 535341429929) ^ 12449800696 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 535341429929) ^ 344 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_571773041407 : Nat.Prime 571773041407 := by
  apply lucas_primality 571773041407 (5 : ZMod 571773041407)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (821, 1), (325133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (821, 1), (325133, 1)] : List FactorBlock).map factorBlockValue).prod) = 571773041407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_821
      · exact prime_sixtyTwoBH_325133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 571773041407) ^ 285886520703 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 571773041407) ^ 190591013802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 571773041407) ^ 81681863058 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 571773041407) ^ 33633708318 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 571773041407) ^ 696434886 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 571773041407) ^ 1758582 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_617640332773 : Nat.Prime 617640332773 := by
  apply lucas_primality 617640332773 (2 : ZMod 617640332773)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (27011, 1), (40543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (27011, 1), (40543, 1)] : List FactorBlock).map factorBlockValue).prod) = 617640332773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_27011
      · exact prime_sixtyTwoBH_40543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 617640332773) ^ 308820166386 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 617640332773) ^ 205880110924 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 617640332773) ^ 13141283676 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 617640332773) ^ 22866252 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 617640332773) ^ 15234204 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_623726951539 : Nat.Prime 623726951539 := by
  apply lucas_primality 623726951539 (3 : ZMod 623726951539)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103954491923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103954491923, 1)] : List FactorBlock).map factorBlockValue).prod) = 623726951539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_103954491923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 623726951539) ^ 311863475769 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 623726951539) ^ 207908983846 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 623726951539) ^ 6 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_689356997713 : Nat.Prime 689356997713 := by
  apply lucas_primality 689356997713 (5 : ZMod 689356997713)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (19, 1), (73, 1), (127, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (19, 1), (73, 1), (127, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) = 689356997713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_127
      · exact prime_sixtyTwoBH_9059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 689356997713) ^ 344678498856 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 689356997713) ^ 229785665904 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 689356997713) ^ 36281947248 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 689356997713) ^ 9443246544 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 689356997713) ^ 5428007856 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 689356997713) ^ 76096368 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_770707912199 : Nat.Prime 770707912199 := by
  apply lucas_primality 770707912199 (7 : ZMod 770707912199)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13219, 1), (594929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13219, 1), (594929, 1)] : List FactorBlock).map factorBlockValue).prod) = 770707912199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_13219
      · exact prime_sixtyTwoBH_594929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 770707912199) ^ 385353956099 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 770707912199) ^ 110101130314 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 770707912199) ^ 58303042 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 770707912199) ^ 1295462 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1065373812929 : Nat.Prime 1065373812929 := by
  apply lucas_primality 1065373812929 (3 : ZMod 1065373812929)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29, 1), (574016063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29, 1), (574016063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065373812929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_574016063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1065373812929) ^ 532686906464 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1065373812929) ^ 36737028032 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1065373812929) ^ 1856 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1276839411823 : Nat.Prime 1276839411823 := by
  apply lucas_primality 1276839411823 (5 : ZMod 1276839411823)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (1818859561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (1818859561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276839411823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_1818859561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1276839411823) ^ 638419705911 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1276839411823) ^ 425613137274 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1276839411823) ^ 98218416294 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1276839411823) ^ 702 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1592212307897 : Nat.Prime 1592212307897 := by
  apply lucas_primality 1592212307897 (3 : ZMod 1592212307897)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (101, 1), (173, 1), (85643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (101, 1), (173, 1), (85643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1592212307897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_101
      · exact prime_sixtyTwoBH_173
      · exact prime_sixtyTwoBH_85643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1592212307897) ^ 796106153948 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1592212307897) ^ 227458901128 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1592212307897) ^ 83800647784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1592212307897) ^ 15764478296 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1592212307897) ^ 9203539352 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1592212307897) ^ 18591272 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1835823623509 : Nat.Prime 1835823623509 := by
  apply lucas_primality 1835823623509 (6 : ZMod 1835823623509)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (57119, 1), (127541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (57119, 1), (127541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1835823623509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_57119
      · exact prime_sixtyTwoBH_127541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1835823623509) ^ 917911811754 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835823623509) ^ 611941207836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835823623509) ^ 262260517644 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835823623509) ^ 32140332 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1835823623509) ^ 14393988 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2410761589673 : Nat.Prime 2410761589673 := by
  apply lucas_primality 2410761589673 (3 : ZMod 2410761589673)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (301345198709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (301345198709, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410761589673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_301345198709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2410761589673) ^ 1205380794836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2410761589673) ^ 8 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2615857079821 : Nat.Prime 2615857079821 := by
  apply lucas_primality 2615857079821 (6 : ZMod 2615857079821)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 1), (288725947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 1), (288725947, 1)] : List FactorBlock).map factorBlockValue).prod) = 2615857079821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_288725947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2615857079821) ^ 1307928539910 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2615857079821) ^ 871952359940 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2615857079821) ^ 523171415964 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2615857079821) ^ 17323556820 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2615857079821) ^ 9060 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2728727436817 : Nat.Prime 2728727436817 := by
  apply lucas_primality 2728727436817 (5 : ZMod 2728727436817)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (27803, 1), (681563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (27803, 1), (681563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2728727436817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_27803
      · exact prime_sixtyTwoBH_681563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2728727436817) ^ 1364363718408 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2728727436817) ^ 909575812272 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2728727436817) ^ 98145072 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2728727436817) ^ 4003632 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2757427990853 : Nat.Prime 2757427990853 := by
  apply lucas_primality 2757427990853 (2 : ZMod 2757427990853)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (689356997713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (689356997713, 1)] : List FactorBlock).map factorBlockValue).prod) = 2757427990853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_689356997713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2757427990853) ^ 1378713995426 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2757427990853) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2787965901629 : Nat.Prime 2787965901629 := by
  apply lucas_primality 2787965901629 (2 : ZMod 2787965901629)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (4028852459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (4028852459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2787965901629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_173
      · exact prime_sixtyTwoBH_4028852459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2787965901629) ^ 1393982950814 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2787965901629) ^ 16115409836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2787965901629) ^ 692 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3067637435407 : Nat.Prime 3067637435407 := by
  apply lucas_primality 3067637435407 (3 : ZMod 3067637435407)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (631, 1), (1069, 1), (3461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (631, 1), (1069, 1), (3461, 1)] : List FactorBlock).map factorBlockValue).prod) = 3067637435407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_631
      · exact prime_sixtyTwoBH_1069
      · exact prime_sixtyTwoBH_3461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3067637435407) ^ 1533818717703 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3067637435407) ^ 1022545811802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3067637435407) ^ 42022430622 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3067637435407) ^ 4861549026 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3067637435407) ^ 2869632774 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3067637435407) ^ 886344246 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3277984244077 : Nat.Prime 3277984244077 := by
  apply lucas_primality 3277984244077 (5 : ZMod 3277984244077)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (1373, 1), (839473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (1373, 1), (839473, 1)] : List FactorBlock).map factorBlockValue).prod) = 3277984244077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_79
      · exact prime_sixtyTwoBH_1373
      · exact prime_sixtyTwoBH_839473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3277984244077) ^ 1638992122038 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3277984244077) ^ 1092661414692 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3277984244077) ^ 41493471444 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3277984244077) ^ 2387461212 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3277984244077) ^ 3904812 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_4255675833677 : Nat.Prime 4255675833677 := by
  apply lucas_primality 4255675833677 (2 : ZMod 4255675833677)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (650873, 1), (1634603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (650873, 1), (1634603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4255675833677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_650873
      · exact prime_sixtyTwoBH_1634603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4255675833677) ^ 2127837916838 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4255675833677) ^ 6538412 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4255675833677) ^ 2603492 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6436458004793 : Nat.Prime 6436458004793 := by
  apply lucas_primality 6436458004793 (3 : ZMod 6436458004793)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (33119, 1), (458357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (33119, 1), (458357, 1)] : List FactorBlock).map factorBlockValue).prod) = 6436458004793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_53
      · exact prime_sixtyTwoBH_33119
      · exact prime_sixtyTwoBH_458357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6436458004793) ^ 3218229002396 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6436458004793) ^ 121442603864 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6436458004793) ^ 194343368 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6436458004793) ^ 14042456 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6999608045671 : Nat.Prime 6999608045671 := by
  apply lucas_primality 6999608045671 (12 : ZMod 6999608045671)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (1545167339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (1545167339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6999608045671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_1545167339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 6999608045671) ^ 3499804022835 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 6999608045671) ^ 2333202681890 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 6999608045671) ^ 1399921609134 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 6999608045671) ^ 46355020170 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 6999608045671) ^ 4530 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_8662080487673 : Nat.Prime 8662080487673 := by
  apply lucas_primality 8662080487673 (3 : ZMod 8662080487673)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (347, 1), (3120345997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (347, 1), (3120345997, 1)] : List FactorBlock).map factorBlockValue).prod) = 8662080487673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_347
      · exact prime_sixtyTwoBH_3120345997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8662080487673) ^ 4331040243836 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8662080487673) ^ 24962767976 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8662080487673) ^ 2776 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9211127402189 : Nat.Prime 9211127402189 := by
  apply lucas_primality 9211127402189 (2 : ZMod 9211127402189)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (94321, 1), (126499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (94321, 1), (126499, 1)] : List FactorBlock).map factorBlockValue).prod) = 9211127402189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_193
      · exact prime_sixtyTwoBH_94321
      · exact prime_sixtyTwoBH_126499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9211127402189) ^ 4605563701094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9211127402189) ^ 47726048716 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9211127402189) ^ 97657228 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9211127402189) ^ 72815812 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_13827182852759 : Nat.Prime 13827182852759 := by
  apply lucas_primality 13827182852759 (11 : ZMod 13827182852759)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (67, 1), (9380721067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (67, 1), (9380721067, 1)] : List FactorBlock).map factorBlockValue).prod) = 13827182852759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_9380721067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 13827182852759) ^ 6913591426379 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 13827182852759) ^ 1257016622978 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 13827182852759) ^ 206375863474 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 13827182852759) ^ 1474 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_21500162287861 : Nat.Prime 21500162287861 := by
  apply lucas_primality 21500162287861 (6 : ZMod 21500162287861)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19489, 1), (18386579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19489, 1), (18386579, 1)] : List FactorBlock).map factorBlockValue).prod) = 21500162287861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_19489
      · exact prime_sixtyTwoBH_18386579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21500162287861) ^ 10750081143930 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 21500162287861) ^ 7166720762620 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 21500162287861) ^ 4300032457572 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 21500162287861) ^ 1103194740 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 21500162287861) ^ 1169340 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_21688415101849 : Nat.Prime 21688415101849 := by
  apply lucas_primality 21688415101849 (7 : ZMod 21688415101849)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (31, 1), (191, 1), (13874867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (31, 1), (191, 1), (13874867, 1)] : List FactorBlock).map factorBlockValue).prod) = 21688415101849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_191
      · exact prime_sixtyTwoBH_13874867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21688415101849) ^ 10844207550924 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 21688415101849) ^ 7229471700616 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 21688415101849) ^ 1971674100168 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 21688415101849) ^ 699626293608 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 21688415101849) ^ 113551911528 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 21688415101849) ^ 1563144 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_27168535124077 : Nat.Prime 27168535124077 := by
  apply lucas_primality 27168535124077 (11 : ZMod 27168535124077)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5171, 1), (437834963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5171, 1), (437834963, 1)] : List FactorBlock).map factorBlockValue).prod) = 27168535124077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5171
      · exact prime_sixtyTwoBH_437834963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 27168535124077) ^ 13584267562038 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 27168535124077) ^ 9056178374692 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 27168535124077) ^ 5254019556 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 27168535124077) ^ 62052 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_36796455632513 : Nat.Prime 36796455632513 := by
  apply lucas_primality 36796455632513 (3 : ZMod 36796455632513)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (239, 1), (491, 1), (36563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (239, 1), (491, 1), (36563, 1)] : List FactorBlock).map factorBlockValue).prod) = 36796455632513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_239
      · exact prime_sixtyTwoBH_491
      · exact prime_sixtyTwoBH_36563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36796455632513) ^ 18398227816256 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36796455632513) ^ 549200830336 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36796455632513) ^ 153960065408 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36796455632513) ^ 74941864832 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 36796455632513) ^ 1006385024 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_37372759943747 : Nat.Prime 37372759943747 := by
  apply lucas_primality 37372759943747 (2 : ZMod 37372759943747)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89821, 1), (208040213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89821, 1), (208040213, 1)] : List FactorBlock).map factorBlockValue).prod) = 37372759943747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_89821
      · exact prime_sixtyTwoBH_208040213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37372759943747) ^ 18686379971873 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37372759943747) ^ 416080426 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37372759943747) ^ 179642 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_37778995937069 : Nat.Prime 37778995937069 := by
  apply lucas_primality 37778995937069 (2 : ZMod 37778995937069)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14629, 1), (645618223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14629, 1), (645618223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37778995937069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_14629
      · exact prime_sixtyTwoBH_645618223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37778995937069) ^ 18889497968534 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37778995937069) ^ 2582472892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37778995937069) ^ 58516 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_40493569454573 : Nat.Prime 40493569454573 := by
  apply lucas_primality 40493569454573 (2 : ZMod 40493569454573)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (61, 1), (1061, 1), (12031991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (61, 1), (1061, 1), (12031991, 1)] : List FactorBlock).map factorBlockValue).prod) = 40493569454573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_1061
      · exact prime_sixtyTwoBH_12031991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40493569454573) ^ 20246784727286 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40493569454573) ^ 3114889958044 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40493569454573) ^ 663829007452 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40493569454573) ^ 38165475452 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40493569454573) ^ 3365492 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_41847012708481 : Nat.Prime 41847012708481 := by
  apply lucas_primality 41847012708481 (17 : ZMod 41847012708481)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (7, 2), (1291, 1), (114847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (7, 2), (1291, 1), (114847, 1)] : List FactorBlock).map factorBlockValue).prod) = 41847012708481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_1291
      · exact prime_sixtyTwoBH_114847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 41847012708481) ^ 20923506354240 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41847012708481) ^ 13949004236160 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41847012708481) ^ 8369402541696 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41847012708481) ^ 5978144672640 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41847012708481) ^ 32414417280 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41847012708481) ^ 364371840 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_52447747905233 : Nat.Prime 52447747905233 := by
  apply lucas_primality 52447747905233 (3 : ZMod 52447747905233)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3277984244077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3277984244077, 1)] : List FactorBlock).map factorBlockValue).prod) = 52447747905233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3277984244077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 52447747905233) ^ 26223873952616 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52447747905233) ^ 16 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_53045730141409 : Nat.Prime 53045730141409 := by
  apply lucas_primality 53045730141409 (7 : ZMod 53045730141409)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (439, 1), (139853123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (439, 1), (139853123, 1)] : List FactorBlock).map factorBlockValue).prod) = 53045730141409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_439
      · exact prime_sixtyTwoBH_139853123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53045730141409) ^ 26522865070704 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 53045730141409) ^ 17681910047136 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 53045730141409) ^ 120833098272 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 53045730141409) ^ 379296 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_54810676437581 : Nat.Prime 54810676437581 := by
  apply lucas_primality 54810676437581 (3 : ZMod 54810676437581)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (139, 1), (402368789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (139, 1), (402368789, 1)] : List FactorBlock).map factorBlockValue).prod) = 54810676437581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_139
      · exact prime_sixtyTwoBH_402368789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54810676437581) ^ 27405338218790 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 54810676437581) ^ 10962135287516 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 54810676437581) ^ 7830096633940 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 54810676437581) ^ 394321413220 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 54810676437581) ^ 136220 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_55217473837327 : Nat.Prime 55217473837327 := by
  apply lucas_primality 55217473837327 (3 : ZMod 55217473837327)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3067637435407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3067637435407, 1)] : List FactorBlock).map factorBlockValue).prod) = 55217473837327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_3067637435407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55217473837327) ^ 27608736918663 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55217473837327) ^ 18405824612442 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55217473837327) ^ 18 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_58232995172977 : Nat.Prime 58232995172977 := by
  apply lucas_primality 58232995172977 (5 : ZMod 58232995172977)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (60383, 1), (1545503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (60383, 1), (1545503, 1)] : List FactorBlock).map factorBlockValue).prod) = 58232995172977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_60383
      · exact prime_sixtyTwoBH_1545503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58232995172977) ^ 29116497586488 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58232995172977) ^ 19410998390992 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58232995172977) ^ 4479461167152 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58232995172977) ^ 964393872 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 58232995172977) ^ 37678992 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_65450207258983 : Nat.Prime 65450207258983 := by
  apply lucas_primality 65450207258983 (3 : ZMod 65450207258983)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (181, 1), (659, 1), (334991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (181, 1), (659, 1), (334991, 1)] : List FactorBlock).map factorBlockValue).prod) = 65450207258983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_181
      · exact prime_sixtyTwoBH_659
      · exact prime_sixtyTwoBH_334991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65450207258983) ^ 32725103629491 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 21816735752994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 9350029608426 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 5034631327614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 361603355022 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 99317461698 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65450207258983) ^ 195379002 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_77958701301427 : Nat.Prime 77958701301427 := by
  apply lucas_primality 77958701301427 (3 : ZMod 77958701301427)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (239, 1), (4942227799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (239, 1), (4942227799, 1)] : List FactorBlock).map factorBlockValue).prod) = 77958701301427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_239
      · exact prime_sixtyTwoBH_4942227799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 77958701301427) ^ 38979350650713 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 77958701301427) ^ 25986233767142 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 77958701301427) ^ 7087154663766 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 77958701301427) ^ 326187034734 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 77958701301427) ^ 15774 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_116069048104531 : Nat.Prime 116069048104531 := by
  apply lucas_primality 116069048104531 (2 : ZMod 116069048104531)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (80627, 1), (1020979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (80627, 1), (1020979, 1)] : List FactorBlock).map factorBlockValue).prod) = 116069048104531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_80627
      · exact prime_sixtyTwoBH_1020979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116069048104531) ^ 58034524052265 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116069048104531) ^ 38689682701510 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116069048104531) ^ 23213809620906 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116069048104531) ^ 2469554214990 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116069048104531) ^ 1439580390 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 116069048104531) ^ 113684070 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_142643991397393 : Nat.Prime 142643991397393 := by
  apply lucas_primality 142643991397393 (13 : ZMod 142643991397393)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (17, 1), (29, 1), (67, 1), (3332167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (17, 1), (29, 1), (67, 1), (3332167, 1)] : List FactorBlock).map factorBlockValue).prod) = 142643991397393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_3332167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 142643991397393) ^ 71321995698696 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 142643991397393) ^ 47547997132464 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 142643991397393) ^ 8390823023376 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 142643991397393) ^ 4918758324048 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 142643991397393) ^ 2129014796976 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 142643991397393) ^ 42808176 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_215059476225959 : Nat.Prime 215059476225959 := by
  apply lucas_primality 215059476225959 (7 : ZMod 215059476225959)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (811, 1), (997, 1), (1461407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (811, 1), (997, 1), (1461407, 1)] : List FactorBlock).map factorBlockValue).prod) = 215059476225959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_811
      · exact prime_sixtyTwoBH_997
      · exact prime_sixtyTwoBH_1461407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 215059476225959) ^ 107529738112979 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 215059476225959) ^ 30722782317994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 215059476225959) ^ 16543036632766 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 215059476225959) ^ 265178145778 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 215059476225959) ^ 215706596014 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 215059476225959) ^ 147159194 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_221421359946967 : Nat.Prime 221421359946967 := by
  apply lucas_primality 221421359946967 (3 : ZMod 221421359946967)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (14713, 1), (34359289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (14713, 1), (34359289, 1)] : List FactorBlock).map factorBlockValue).prod) = 221421359946967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_14713
      · exact prime_sixtyTwoBH_34359289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 221421359946967) ^ 110710679973483 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221421359946967) ^ 73807119982322 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221421359946967) ^ 3033169314342 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221421359946967) ^ 15049368582 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221421359946967) ^ 6444294 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_234688233423947 : Nat.Prime 234688233423947 := by
  apply lucas_primality 234688233423947 (2 : ZMod 234688233423947)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (31, 1), (130527382327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (31, 1), (130527382327, 1)] : List FactorBlock).map factorBlockValue).prod) = 234688233423947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_130527382327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 234688233423947) ^ 117344116711973 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 234688233423947) ^ 8092697704274 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 234688233423947) ^ 7570588174966 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 234688233423947) ^ 1798 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_243679546004819 : Nat.Prime 243679546004819 := by
  apply lucas_primality 243679546004819 (2 : ZMod 243679546004819)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (71, 1), (3183772061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (71, 1), (3183772061, 1)] : List FactorBlock).map factorBlockValue).prod) = 243679546004819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_71
      · exact prime_sixtyTwoBH_3183772061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 243679546004819) ^ 121839773002409 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243679546004819) ^ 34811363714974 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243679546004819) ^ 22152686000438 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243679546004819) ^ 3432106281758 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243679546004819) ^ 76538 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_278854434334199 : Nat.Prime 278854434334199 := by
  apply lucas_primality 278854434334199 (11 : ZMod 278854434334199)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (691, 1), (201776001689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (691, 1), (201776001689, 1)] : List FactorBlock).map factorBlockValue).prod) = 278854434334199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_691
      · exact prime_sixtyTwoBH_201776001689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 278854434334199) ^ 139427217167099 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 278854434334199) ^ 403552003378 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 278854434334199) ^ 1382 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_311834805205709 : Nat.Prime 311834805205709 := by
  apply lucas_primality 311834805205709 (2 : ZMod 311834805205709)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (77958701301427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (77958701301427, 1)] : List FactorBlock).map factorBlockValue).prod) = 311834805205709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_77958701301427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 311834805205709) ^ 155917402602854 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 311834805205709) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_314686487431399 : Nat.Prime 314686487431399 := by
  apply lucas_primality 314686487431399 (15 : ZMod 314686487431399)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52447747905233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52447747905233, 1)] : List FactorBlock).map factorBlockValue).prod) = 314686487431399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_52447747905233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 314686487431399) ^ 157343243715699 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 314686487431399) ^ 104895495810466 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 314686487431399) ^ 6 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_426972183358247 : Nat.Prime 426972183358247 := by
  apply lucas_primality 426972183358247 (5 : ZMod 426972183358247)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277, 1), (770707912199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277, 1), (770707912199, 1)] : List FactorBlock).map factorBlockValue).prod) = 426972183358247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_277
      · exact prime_sixtyTwoBH_770707912199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 426972183358247) ^ 213486091679123 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 426972183358247) ^ 1541415824398 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 426972183358247) ^ 554 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_432001390069727 : Nat.Prime 432001390069727 := by
  apply lucas_primality 432001390069727 (5 : ZMod 432001390069727)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47059, 1), (4589997557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47059, 1), (4589997557, 1)] : List FactorBlock).map factorBlockValue).prod) = 432001390069727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_47059
      · exact prime_sixtyTwoBH_4589997557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 432001390069727) ^ 216000695034863 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 432001390069727) ^ 9179995114 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 432001390069727) ^ 94118 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_437907882009457 : Nat.Prime 437907882009457 := by
  apply lucas_primality 437907882009457 (5 : ZMod 437907882009457)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (6197, 1), (490725667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (6197, 1), (490725667, 1)] : List FactorBlock).map factorBlockValue).prod) = 437907882009457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_6197
      · exact prime_sixtyTwoBH_490725667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 437907882009457) ^ 218953941004728 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 437907882009457) ^ 145969294003152 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 437907882009457) ^ 70664496048 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 437907882009457) ^ 892368 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_478768140818711 : Nat.Prime 478768140818711 := by
  apply lucas_primality 478768140818711 (7 : ZMod 478768140818711)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2723779, 1), (17577349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2723779, 1), (17577349, 1)] : List FactorBlock).map factorBlockValue).prod) = 478768140818711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_2723779
      · exact prime_sixtyTwoBH_17577349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 478768140818711) ^ 239384070409355 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 478768140818711) ^ 95753628163742 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 478768140818711) ^ 175773490 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 478768140818711) ^ 27237790 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_486509613795743 : Nat.Prime 486509613795743 := by
  apply lucas_primality 486509613795743 (5 : ZMod 486509613795743)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (4793, 1), (1371678331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (4793, 1), (1371678331, 1)] : List FactorBlock).map factorBlockValue).prod) = 486509613795743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_4793
      · exact prime_sixtyTwoBH_1371678331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 486509613795743) ^ 243254806897871 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 486509613795743) ^ 13148908480966 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 486509613795743) ^ 101504196494 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 486509613795743) ^ 354682 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_592877815684417 : Nat.Prime 592877815684417 := by
  apply lucas_primality 592877815684417 (5 : ZMod 592877815684417)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (59, 1), (17445792599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (59, 1), (17445792599, 1)] : List FactorBlock).map factorBlockValue).prod) = 592877815684417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_59
      · exact prime_sixtyTwoBH_17445792599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 592877815684417) ^ 296438907842208 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 592877815684417) ^ 197625938561472 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 592877815684417) ^ 10048776537024 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 592877815684417) ^ 33984 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_632012760372083 : Nat.Prime 632012760372083 := by
  apply lucas_primality 632012760372083 (2 : ZMod 632012760372083)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1117, 1), (282906338573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1117, 1), (282906338573, 1)] : List FactorBlock).map factorBlockValue).prod) = 632012760372083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_1117
      · exact prime_sixtyTwoBH_282906338573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 632012760372083) ^ 316006380186041 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 632012760372083) ^ 565812677146 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 632012760372083) ^ 2234 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_697181239589449 : Nat.Prime 697181239589449 := by
  apply lucas_primality 697181239589449 (7 : ZMod 697181239589449)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37189, 1), (781123943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37189, 1), (781123943, 1)] : List FactorBlock).map factorBlockValue).prod) = 697181239589449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_37189
      · exact prime_sixtyTwoBH_781123943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 697181239589449) ^ 348590619794724 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 697181239589449) ^ 232393746529816 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 697181239589449) ^ 18746974632 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 697181239589449) ^ 892536 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_704880613782487 : Nat.Prime 704880613782487 := by
  apply lucas_primality 704880613782487 (3 : ZMod 704880613782487)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 2), (311, 1), (1019, 1), (27527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 2), (311, 1), (1019, 1), (27527, 1)] : List FactorBlock).map factorBlockValue).prod) = 704880613782487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_311
      · exact prime_sixtyTwoBH_1019
      · exact prime_sixtyTwoBH_27527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 704880613782487) ^ 352440306891243 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704880613782487) ^ 234960204594162 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704880613782487) ^ 10520606175858 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704880613782487) ^ 2266497150426 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704880613782487) ^ 691737599394 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704880613782487) ^ 25606881018 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_959767938685519 : Nat.Prime 959767938685519 := by
  apply lucas_primality 959767938685519 (3 : ZMod 959767938685519)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (928153, 1), (172343701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (928153, 1), (172343701, 1)] : List FactorBlock).map factorBlockValue).prod) = 959767938685519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_928153
      · exact prime_sixtyTwoBH_172343701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 959767938685519) ^ 479883969342759 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 959767938685519) ^ 319922646228506 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 959767938685519) ^ 1034062206 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 959767938685519) ^ 5568918 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_976961322368399 : Nat.Prime 976961322368399 := by
  apply lucas_primality 976961322368399 (7 : ZMod 976961322368399)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (51827, 1), (554424461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (51827, 1), (554424461, 1)] : List FactorBlock).map factorBlockValue).prod) = 976961322368399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_51827
      · exact prime_sixtyTwoBH_554424461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 976961322368399) ^ 488480661184199 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 976961322368399) ^ 57468313080494 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 976961322368399) ^ 18850431674 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 976961322368399) ^ 1762118 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1119943692833983 : Nat.Prime 1119943692833983 := by
  apply lucas_primality 1119943692833983 (12 : ZMod 1119943692833983)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (6436458004793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (6436458004793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119943692833983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_6436458004793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 1119943692833983) ^ 559971846416991 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1119943692833983) ^ 373314564277994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1119943692833983) ^ 38618748028758 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1119943692833983) ^ 174 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1264025520744167 : Nat.Prime 1264025520744167 := by
  apply lucas_primality 1264025520744167 (5 : ZMod 1264025520744167)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (632012760372083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (632012760372083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264025520744167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_632012760372083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1264025520744167) ^ 632012760372083 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264025520744167) ^ 2 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1419010710998827 : Nat.Prime 1419010710998827 := by
  apply lucas_primality 1419010710998827 (2 : ZMod 1419010710998827)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (21500162287861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (21500162287861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1419010710998827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_21500162287861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1419010710998827) ^ 709505355499413 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419010710998827) ^ 473003570332942 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419010710998827) ^ 129000973727166 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419010710998827) ^ 66 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1438653674882533 : Nat.Prime 1438653674882533 := by
  apply lucas_primality 1438653674882533 (2 : ZMod 1438653674882533)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (89, 1), (97, 1), (816891451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (89, 1), (97, 1), (816891451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1438653674882533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_89
      · exact prime_sixtyTwoBH_97
      · exact prime_sixtyTwoBH_816891451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1438653674882533) ^ 719326837441266 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438653674882533) ^ 479551224960844 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438653674882533) ^ 84626686757796 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438653674882533) ^ 16164648032388 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438653674882533) ^ 14831481184356 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438653674882533) ^ 1761132 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1439377411225267 : Nat.Prime 1439377411225267 := by
  apply lucas_primality 1439377411225267 (2 : ZMod 1439377411225267)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (2757427990853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (2757427990853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439377411225267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_2757427990853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1439377411225267) ^ 719688705612633 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439377411225267) ^ 479792470408422 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439377411225267) ^ 49633703835354 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1439377411225267) ^ 522 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2691915261409597 : Nat.Prime 2691915261409597 := by
  apply lucas_primality 2691915261409597 (2 : ZMod 2691915261409597)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (631, 1), (1063, 1), (334439461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (631, 1), (1063, 1), (334439461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2691915261409597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_631
      · exact prime_sixtyTwoBH_1063
      · exact prime_sixtyTwoBH_334439461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2691915261409597) ^ 1345957630704798 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2691915261409597) ^ 897305087136532 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2691915261409597) ^ 4266109764516 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2691915261409597) ^ 2532375598692 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2691915261409597) ^ 8049036 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3313327516904323 : Nat.Prime 3313327516904323 := by
  apply lucas_primality 3313327516904323 (2 : ZMod 3313327516904323)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 2), (237067, 1), (2150867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 2), (237067, 1), (2150867, 1)] : List FactorBlock).map factorBlockValue).prod) = 3313327516904323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_237067
      · exact prime_sixtyTwoBH_2150867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3313327516904323) ^ 1656663758452161 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313327516904323) ^ 1104442505634774 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313327516904323) ^ 174385658784438 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313327516904323) ^ 13976333766 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313327516904323) ^ 1540461366 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3771420986484961 : Nat.Prime 3771420986484961 := by
  apply lucas_primality 3771420986484961 (7 : ZMod 3771420986484961)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (59, 1), (133171645003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (59, 1), (133171645003, 1)] : List FactorBlock).map factorBlockValue).prod) = 3771420986484961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_59
      · exact prime_sixtyTwoBH_133171645003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3771420986484961) ^ 1885710493242480 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3771420986484961) ^ 1257140328828320 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3771420986484961) ^ 754284197296992 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3771420986484961) ^ 63922389601440 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3771420986484961) ^ 28320 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_5161427429423017 : Nat.Prime 5161427429423017 := by
  apply lucas_primality 5161427429423017 (10 : ZMod 5161427429423017)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (215059476225959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (215059476225959, 1)] : List FactorBlock).map factorBlockValue).prod) = 5161427429423017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_215059476225959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5161427429423017) ^ 2580713714711508 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 5161427429423017) ^ 1720475809807672 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 5161427429423017) ^ 24 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_10767661045638389 : Nat.Prime 10767661045638389 := by
  apply lucas_primality 10767661045638389 (2 : ZMod 10767661045638389)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2691915261409597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2691915261409597, 1)] : List FactorBlock).map factorBlockValue).prod) = 10767661045638389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_2691915261409597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10767661045638389) ^ 5383830522819194 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10767661045638389) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_12549262312610083 : Nat.Prime 12549262312610083 := by
  apply lucas_primality 12549262312610083 (2 : ZMod 12549262312610083)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (697181239589449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (697181239589449, 1)] : List FactorBlock).map factorBlockValue).prod) = 12549262312610083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_697181239589449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12549262312610083) ^ 6274631156305041 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12549262312610083) ^ 4183087437536694 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12549262312610083) ^ 18 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_13253310067617293 : Nat.Prime 13253310067617293 := by
  apply lucas_primality 13253310067617293 (2 : ZMod 13253310067617293)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3313327516904323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3313327516904323, 1)] : List FactorBlock).map factorBlockValue).prod) = 13253310067617293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3313327516904323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13253310067617293) ^ 6626655033808646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13253310067617293) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_17232372549902663 : Nat.Prime 17232372549902663 := by
  apply lucas_primality 17232372549902663 (5 : ZMod 17232372549902663)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (61, 1), (1039, 1), (7996883617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (61, 1), (1039, 1), (7996883617, 1)] : List FactorBlock).map factorBlockValue).prod) = 17232372549902663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_1039
      · exact prime_sixtyTwoBH_7996883617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17232372549902663) ^ 8616186274951331 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17232372549902663) ^ 1013668973523686 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17232372549902663) ^ 282497910654142 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17232372549902663) ^ 16585536621658 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17232372549902663) ^ 2154886 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_29060516272098781 : Nat.Prime 29060516272098781 := by
  apply lucas_primality 29060516272098781 (6 : ZMod 29060516272098781)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (7, 1), (31, 1), (61, 1), (4463, 1), (303649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (7, 1), (31, 1), (61, 1), (4463, 1), (303649, 1)] : List FactorBlock).map factorBlockValue).prod) = 29060516272098781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_61
      · exact prime_sixtyTwoBH_4463
      · exact prime_sixtyTwoBH_303649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29060516272098781) ^ 14530258136049390 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 9686838757366260 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 5812103254419756 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 4151502324585540 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 937436008777380 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 476401906099980 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 6511430937060 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 29060516272098781) ^ 95704304220 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_31022990508841343 : Nat.Prime 31022990508841343 := by
  apply lucas_primality 31022990508841343 (10 : ZMod 31022990508841343)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (59, 1), (73, 1), (457, 1), (42142567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (59, 1), (73, 1), (457, 1), (42142567, 1)] : List FactorBlock).map factorBlockValue).prod) = 31022990508841343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_59
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_457
      · exact prime_sixtyTwoBH_42142567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 31022990508841343) ^ 15511495254420671 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 2820271864440122 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 1824881794637726 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 525813398454938 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 424972472723854 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 67884005489806 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 31022990508841343) ^ 736143826 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_31448223278808899 : Nat.Prime 31448223278808899 := by
  apply lucas_primality 31448223278808899 (2 : ZMod 31448223278808899)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (234688233423947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (234688233423947, 1)] : List FactorBlock).map factorBlockValue).prod) = 31448223278808899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_234688233423947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31448223278808899) ^ 15724111639404449 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31448223278808899) ^ 469376466847894 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31448223278808899) ^ 134 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_33423346696273607 : Nat.Prime 33423346696273607 := by
  apply lucas_primality 33423346696273607 (5 : ZMod 33423346696273607)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (541, 1), (929, 1), (5981, 1), (70373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (541, 1), (929, 1), (5981, 1), (70373, 1)] : List FactorBlock).map factorBlockValue).prod) = 33423346696273607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_79
      · exact prime_sixtyTwoBH_541
      · exact prime_sixtyTwoBH_929
      · exact prime_sixtyTwoBH_5981
      · exact prime_sixtyTwoBH_70373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33423346696273607) ^ 16711673348136803 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33423346696273607) ^ 423080337927514 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33423346696273607) ^ 61780677811966 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33423346696273607) ^ 35977768241414 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33423346696273607) ^ 5588253920126 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33423346696273607) ^ 474945599822 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_37317253554457003 : Nat.Prime 37317253554457003 := by
  apply lucas_primality 37317253554457003 (2 : ZMod 37317253554457003)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (3389, 1), (9710130127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (3389, 1), (9710130127, 1)] : List FactorBlock).map factorBlockValue).prod) = 37317253554457003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_3389
      · exact prime_sixtyTwoBH_9710130127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37317253554457003) ^ 18658626777228501 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37317253554457003) ^ 12439084518152334 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37317253554457003) ^ 5331036222065286 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37317253554457003) ^ 11011287564018 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 37317253554457003) ^ 3843126 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_51652695137778937 : Nat.Prime 51652695137778937 := by
  apply lucas_primality 51652695137778937 (5 : ZMod 51652695137778937)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1803127, 1), (397863569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1803127, 1), (397863569, 1)] : List FactorBlock).map factorBlockValue).prod) = 51652695137778937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1803127
      · exact prime_sixtyTwoBH_397863569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 51652695137778937) ^ 25826347568889468 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 51652695137778937) ^ 17217565045926312 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 51652695137778937) ^ 28646176968 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 51652695137778937) ^ 129825144 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_106536768542534581 : Nat.Prime 106536768542534581 := by
  apply lucas_primality 106536768542534581 (6 : ZMod 106536768542534581)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (47, 1), (37778995937069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (47, 1), (37778995937069, 1)] : List FactorBlock).map factorBlockValue).prod) = 106536768542534581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_37778995937069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 106536768542534581) ^ 53268384271267290 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 106536768542534581) ^ 35512256180844860 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 106536768542534581) ^ 21307353708506916 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 106536768542534581) ^ 2266739756224140 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 106536768542534581) ^ 2820 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_111398264425694203 : Nat.Prime 111398264425694203 := by
  apply lucas_primality 111398264425694203 (2 : ZMod 111398264425694203)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (132241, 1), (12763458317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (132241, 1), (12763458317, 1)] : List FactorBlock).map factorBlockValue).prod) = 111398264425694203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_132241
      · exact prime_sixtyTwoBH_12763458317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111398264425694203) ^ 55699132212847101 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 111398264425694203) ^ 37132754808564734 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 111398264425694203) ^ 10127114947790382 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 111398264425694203) ^ 842388248922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 111398264425694203) ^ 8727906 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_172083273954000037 : Nat.Prime 172083273954000037 := by
  apply lucas_primality 172083273954000037 (2 : ZMod 172083273954000037)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (160649, 1), (89264625547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (160649, 1), (89264625547, 1)] : List FactorBlock).map factorBlockValue).prod) = 172083273954000037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_160649
      · exact prime_sixtyTwoBH_89264625547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 172083273954000037) ^ 86041636977000018 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 172083273954000037) ^ 57361091318000012 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 172083273954000037) ^ 1071175506564 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 172083273954000037) ^ 1927788 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_229954481290187729 : Nat.Prime 229954481290187729 := by
  apply lucas_primality 229954481290187729 (3 : ZMod 229954481290187729)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 2), (27168535124077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 2), (27168535124077, 1)] : List FactorBlock).map factorBlockValue).prod) = 229954481290187729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_23
      · exact prime_sixtyTwoBH_27168535124077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 229954481290187729) ^ 114977240645093864 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 229954481290187729) ^ 9998020925660336 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 229954481290187729) ^ 8464 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_309256520891766803 : Nat.Prime 309256520891766803 := by
  apply lucas_primality 309256520891766803 (2 : ZMod 309256520891766803)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (3771420986484961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (3771420986484961, 1)] : List FactorBlock).map factorBlockValue).prod) = 309256520891766803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_3771420986484961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 309256520891766803) ^ 154628260445883401 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 309256520891766803) ^ 7542841972969922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 309256520891766803) ^ 82 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_585972229872616703 : Nat.Prime 585972229872616703 := by
  apply lucas_primality 585972229872616703 (5 : ZMod 585972229872616703)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (281, 1), (541, 1), (41005828973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (281, 1), (541, 1), (41005828973, 1)] : List FactorBlock).map factorBlockValue).prod) = 585972229872616703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_281
      · exact prime_sixtyTwoBH_541
      · exact prime_sixtyTwoBH_41005828973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 585972229872616703) ^ 292986114936308351 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 585972229872616703) ^ 12467494252608866 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 585972229872616703) ^ 2085310426592942 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 585972229872616703) ^ 1083127966492822 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 585972229872616703) ^ 14289974 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_832115047673648983 : Nat.Prime 832115047673648983 := by
  apply lucas_primality 832115047673648983 (5 : ZMod 832115047673648983)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3769, 1), (36796455632513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3769, 1), (36796455632513, 1)] : List FactorBlock).map factorBlockValue).prod) = 832115047673648983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_3769
      · exact prime_sixtyTwoBH_36796455632513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 832115047673648983) ^ 416057523836824491 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 832115047673648983) ^ 277371682557882994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 832115047673648983) ^ 220778733795078 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 832115047673648983) ^ 22614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1008224084684187769 : Nat.Prime 1008224084684187769 := by
  apply lucas_primality 1008224084684187769 (11 : ZMod 1008224084684187769)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (976961322368399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (976961322368399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008224084684187769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_976961322368399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1008224084684187769) ^ 504112042342093884 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1008224084684187769) ^ 336074694894729256 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1008224084684187769) ^ 23447071736841576 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1008224084684187769) ^ 1032 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1039895309177094947 : Nat.Prime 1039895309177094947 := by
  apply lucas_primality 1039895309177094947 (2 : ZMod 1039895309177094947)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7561, 1), (24767, 1), (2776559479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7561, 1), (24767, 1), (2776559479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039895309177094947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7561
      · exact prime_sixtyTwoBH_24767
      · exact prime_sixtyTwoBH_2776559479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1039895309177094947) ^ 519947654588547473 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039895309177094947) ^ 137534097232786 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039895309177094947) ^ 41987132441438 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039895309177094947) ^ 374526574 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1239481855089521947 : Nat.Prime 1239481855089521947 := by
  apply lucas_primality 1239481855089521947 (3 : ZMod 1239481855089521947)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (5309, 1), (617640332773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (5309, 1), (617640332773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239481855089521947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_5309
      · exact prime_sixtyTwoBH_617640332773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1239481855089521947) ^ 619740927544760973 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1239481855089521947) ^ 413160618363173982 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1239481855089521947) ^ 177068836441360278 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1239481855089521947) ^ 233468045788194 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1239481855089521947) ^ 2006802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1243320687929717071 : Nat.Prime 1243320687929717071 := by
  apply lucas_primality 1243320687929717071 (21 : ZMod 1243320687929717071)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4085827, 1), (10143362147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4085827, 1), (10143362147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243320687929717071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_4085827
      · exact prime_sixtyTwoBH_10143362147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 1243320687929717071) ^ 621660343964858535 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1243320687929717071) ^ 414440229309905690 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1243320687929717071) ^ 248664137585943414 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1243320687929717071) ^ 304300864410 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1243320687929717071) ^ 122574810 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1616741873260201927 : Nat.Prime 1616741873260201927 := by
  apply lucas_primality 1616741873260201927 (5 : ZMod 1616741873260201927)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (41, 1), (139, 1), (1021, 1), (10837, 1), (67829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (41, 1), (139, 1), (1021, 1), (10837, 1), (67829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616741873260201927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_139
      · exact prime_sixtyTwoBH_1021
      · exact prime_sixtyTwoBH_10837
      · exact prime_sixtyTwoBH_67829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1616741873260201927) ^ 808370936630100963 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 538913957753400642 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 230963124751457418 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 39432728616102486 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 11631236498274834 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 1583488612399806 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 149187217242798 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1616741873260201927) ^ 23835555194094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2164470262522233473 : Nat.Prime 2164470262522233473 := by
  apply lucas_primality 2164470262522233473 (3 : ZMod 2164470262522233473)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (6197, 1), (2728727436817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (6197, 1), (2728727436817, 1)] : List FactorBlock).map factorBlockValue).prod) = 2164470262522233473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_6197
      · exact prime_sixtyTwoBH_2728727436817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2164470262522233473) ^ 1082235131261116736 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2164470262522233473) ^ 349277111912576 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2164470262522233473) ^ 793216 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2821961641425352961 : Nat.Prime 2821961641425352961 := by
  apply lucas_primality 2821961641425352961 (3 : ZMod 2821961641425352961)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (19, 1), (406859, 1), (285196117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (19, 1), (406859, 1), (285196117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2821961641425352961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_406859
      · exact prime_sixtyTwoBH_285196117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2821961641425352961) ^ 1410980820712676480 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2821961641425352961) ^ 564392328285070592 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2821961641425352961) ^ 148524296917123840 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2821961641425352961) ^ 6935969565440 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2821961641425352961) ^ 9894810880 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3328460190694595933 : Nat.Prime 3328460190694595933 := by
  apply lucas_primality 3328460190694595933 (2 : ZMod 3328460190694595933)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (832115047673648983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (832115047673648983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3328460190694595933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_832115047673648983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3328460190694595933) ^ 1664230095347297966 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3328460190694595933) ^ 4 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_5539911964211798213 : Nat.Prime 5539911964211798213 := by
  apply lucas_primality 5539911964211798213 (2 : ZMod 5539911964211798213)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (106536768542534581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (106536768542534581, 1)] : List FactorBlock).map factorBlockValue).prod) = 5539911964211798213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_106536768542534581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5539911964211798213) ^ 2769955982105899106 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5539911964211798213) ^ 426147074170138324 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5539911964211798213) ^ 52 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6263224770566407849 : Nat.Prime 6263224770566407849 := by
  apply lucas_primality 6263224770566407849 (11 : ZMod 6263224770566407849)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (593, 1), (47111, 1), (549491297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (593, 1), (47111, 1), (549491297, 1)] : List FactorBlock).map factorBlockValue).prod) = 6263224770566407849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_593
      · exact prime_sixtyTwoBH_47111
      · exact prime_sixtyTwoBH_549491297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6263224770566407849) ^ 3131612385283203924 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6263224770566407849) ^ 2087741590188802616 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6263224770566407849) ^ 368424986503906344 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6263224770566407849) ^ 10561930473130536 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6263224770566407849) ^ 132946122361368 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6263224770566407849) ^ 11398223784 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_8757872083560501607 : Nat.Prime 8757872083560501607 := by
  apply lucas_primality 8757872083560501607 (3 : ZMod 8757872083560501607)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2726569, 1), (535341429929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2726569, 1), (535341429929, 1)] : List FactorBlock).map factorBlockValue).prod) = 8757872083560501607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_2726569
      · exact prime_sixtyTwoBH_535341429929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8757872083560501607) ^ 4378936041780250803 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8757872083560501607) ^ 2919290694520167202 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8757872083560501607) ^ 3212048579574 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8757872083560501607) ^ 16359414 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_12433206879297170711 : Nat.Prime 12433206879297170711 := by
  apply lucas_primality 12433206879297170711 (19 : ZMod 12433206879297170711)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1243320687929717071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1243320687929717071, 1)] : List FactorBlock).map factorBlockValue).prod) = 12433206879297170711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_1243320687929717071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 12433206879297170711) ^ 6216603439648585355 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (19 : ZMod 12433206879297170711) ^ 2486641375859434142 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (19 : ZMod 12433206879297170711) ^ 10 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_15430985952857658767 : Nat.Prime 15430985952857658767 := by
  apply lucas_primality 15430985952857658767 (5 : ZMod 15430985952857658767)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (31, 1), (647, 1), (176459, 1), (18016421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (31, 1), (647, 1), (176459, 1), (18016421, 1)] : List FactorBlock).map factorBlockValue).prod) = 15430985952857658767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_31
      · exact prime_sixtyTwoBH_647
      · exact prime_sixtyTwoBH_176459
      · exact prime_sixtyTwoBH_18016421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15430985952857658767) ^ 7715492976428829383 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15430985952857658767) ^ 1402816904805241706 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15430985952857658767) ^ 497773740414763186 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15430985952857658767) ^ 23850055568558978 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15430985952857658767) ^ 87447996151274 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15430985952857658767) ^ 856495635446 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_20894188004161089367 : Nat.Prime 20894188004161089367 := by
  apply lucas_primality 20894188004161089367 (3 : ZMod 20894188004161089367)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1091, 1), (55501, 1), (8215814953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1091, 1), (55501, 1), (8215814953, 1)] : List FactorBlock).map factorBlockValue).prod) = 20894188004161089367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_1091
      · exact prime_sixtyTwoBH_55501
      · exact prime_sixtyTwoBH_8215814953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20894188004161089367) ^ 10447094002080544683 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20894188004161089367) ^ 6964729334720363122 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20894188004161089367) ^ 2984884000594441338 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20894188004161089367) ^ 19151409719671026 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20894188004161089367) ^ 376465072776366 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20894188004161089367) ^ 2543166822 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_42378043929242305309 : Nat.Prime 42378043929242305309 := by
  apply lucas_primality 42378043929242305309 (6 : ZMod 42378043929242305309)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12212021, 1), (289182573529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12212021, 1), (289182573529, 1)] : List FactorBlock).map factorBlockValue).prod) = 42378043929242305309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_12212021
      · exact prime_sixtyTwoBH_289182573529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42378043929242305309) ^ 21189021964621152654 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 42378043929242305309) ^ 14126014643080768436 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 42378043929242305309) ^ 3470190882348 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 42378043929242305309) ^ 146544252 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_43126593119693132201 : Nat.Prime 43126593119693132201 := by
  apply lucas_primality 43126593119693132201 (15 : ZMod 43126593119693132201)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (41, 1), (829, 1), (23201, 1), (273445049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (41, 1), (829, 1), (23201, 1), (273445049, 1)] : List FactorBlock).map factorBlockValue).prod) = 43126593119693132201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_41
      · exact prime_sixtyTwoBH_829
      · exact prime_sixtyTwoBH_23201
      · exact prime_sixtyTwoBH_273445049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 43126593119693132201) ^ 21563296559846566100 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 43126593119693132201) ^ 8625318623938626440 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 43126593119693132201) ^ 1051868124870564200 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 43126593119693132201) ^ 52022428371161800 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 43126593119693132201) ^ 1858824754092200 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 43126593119693132201) ^ 157715757800 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_43289405250444669461 : Nat.Prime 43289405250444669461 := by
  apply lucas_primality 43289405250444669461 (2 : ZMod 43289405250444669461)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2164470262522233473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2164470262522233473, 1)] : List FactorBlock).map factorBlockValue).prod) = 43289405250444669461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_2164470262522233473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43289405250444669461) ^ 21644702625222334730 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43289405250444669461) ^ 8657881050088933892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43289405250444669461) ^ 20 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_55324595736571414381 : Nat.Prime 55324595736571414381 := by
  apply lucas_primality 55324595736571414381 (10 : ZMod 55324595736571414381)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (16699, 1), (55217473837327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (16699, 1), (55217473837327, 1)] : List FactorBlock).map factorBlockValue).prod) = 55324595736571414381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_16699
      · exact prime_sixtyTwoBH_55217473837327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 55324595736571414381) ^ 27662297868285707190 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 55324595736571414381) ^ 18441531912190471460 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 55324595736571414381) ^ 11064919147314282876 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 55324595736571414381) ^ 3313048430239620 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 55324595736571414381) ^ 1001940 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_67098492758646439861 : Nat.Prime 67098492758646439861 := by
  apply lucas_primality 67098492758646439861 (10 : ZMod 67098492758646439861)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (113, 1), (211, 1), (87018551603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (113, 1), (211, 1), (87018551603, 1)] : List FactorBlock).map factorBlockValue).prod) = 67098492758646439861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_113
      · exact prime_sixtyTwoBH_211
      · exact prime_sixtyTwoBH_87018551603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 67098492758646439861) ^ 33549246379323219930 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 22366164252882146620 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 13419698551729287972 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 9585498965520919980 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 6099862978058767260 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 593791971315455220 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 318002335349035260 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 67098492758646439861) ^ 771082620 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_77687155960015027939 : Nat.Prime 77687155960015027939 := by
  apply lucas_primality 77687155960015027939 (2 : ZMod 77687155960015027939)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (16829, 1), (40493569454573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (16829, 1), (40493569454573, 1)] : List FactorBlock).map factorBlockValue).prod) = 77687155960015027939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_16829
      · exact prime_sixtyTwoBH_40493569454573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77687155960015027939) ^ 38843577980007513969 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77687155960015027939) ^ 25895718653338342646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77687155960015027939) ^ 4088797682106054102 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77687155960015027939) ^ 4616266917821322 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77687155960015027939) ^ 1918506 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_122831789904267378959 : Nat.Prime 122831789904267378959 := by
  apply lucas_primality 122831789904267378959 (13 : ZMod 122831789904267378959)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619, 1), (105461423, 1), (940798267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619, 1), (105461423, 1), (940798267, 1)] : List FactorBlock).map factorBlockValue).prod) = 122831789904267378959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_619
      · exact prime_sixtyTwoBH_105461423
      · exact prime_sixtyTwoBH_940798267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 122831789904267378959) ^ 61415894952133689479 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 122831789904267378959) ^ 198435847987507882 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 122831789904267378959) ^ 1164708254546 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 122831789904267378959) ^ 130561241674 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_132595505595038136979 : Nat.Prime 132595505595038136979 := by
  apply lucas_primality 132595505595038136979 (3 : ZMod 132595505595038136979)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (587, 1), (12549262312610083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (587, 1), (12549262312610083, 1)] : List FactorBlock).map factorBlockValue).prod) = 132595505595038136979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_587
      · exact prime_sixtyTwoBH_12549262312610083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 132595505595038136979) ^ 66297752797519068489 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132595505595038136979) ^ 44198501865012712326 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132595505595038136979) ^ 225886721626981494 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132595505595038136979) ^ 10566 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_556870887381535672573 : Nat.Prime 556870887381535672573 := by
  apply lucas_primality 556870887381535672573 (2 : ZMod 556870887381535672573)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (991, 1), (1419010710998827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (991, 1), (1419010710998827, 1)] : List FactorBlock).map factorBlockValue).prod) = 556870887381535672573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_991
      · exact prime_sixtyTwoBH_1419010710998827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 556870887381535672573) ^ 278435443690767836286 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 556870887381535672573) ^ 185623629127178557524 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 556870887381535672573) ^ 50624626125594152052 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 556870887381535672573) ^ 561928241555535492 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 556870887381535672573) ^ 392436 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_704744779633575650141 : Nat.Prime 704744779633575650141 := by
  apply lucas_primality 704744779633575650141 (3 : ZMod 704744779633575650141)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (73, 1), (6069559, 1), (79528332101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (73, 1), (6069559, 1), (79528332101, 1)] : List FactorBlock).map factorBlockValue).prod) = 704744779633575650141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_73
      · exact prime_sixtyTwoBH_6069559
      · exact prime_sixtyTwoBH_79528332101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 704744779633575650141) ^ 352372389816787825070 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704744779633575650141) ^ 140948955926715130028 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704744779633575650141) ^ 9654038077172269180 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704744779633575650141) ^ 116111364867460 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 704744779633575650141) ^ 8861556140 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_729490353222614854147 : Nat.Prime 729490353222614854147 := by
  apply lucas_primality 729490353222614854147 (7 : ZMod 729490353222614854147)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2309, 1), (144702529, 1), (363888431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2309, 1), (144702529, 1), (363888431, 1)] : List FactorBlock).map factorBlockValue).prod) = 729490353222614854147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_2309
      · exact prime_sixtyTwoBH_144702529
      · exact prime_sixtyTwoBH_363888431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 729490353222614854147) ^ 364745176611307427073 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 729490353222614854147) ^ 243163451074204951382 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 729490353222614854147) ^ 315933457437251994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 729490353222614854147) ^ 5041310323074 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 729490353222614854147) ^ 2004708836766 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_828760197610402346119 : Nat.Prime 828760197610402346119 := by
  apply lucas_primality 828760197610402346119 (3 : ZMod 828760197610402346119)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (1008224084684187769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (1008224084684187769, 1)] : List FactorBlock).map factorBlockValue).prod) = 828760197610402346119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_137
      · exact prime_sixtyTwoBH_1008224084684187769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 828760197610402346119) ^ 414380098805201173059 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 828760197610402346119) ^ 276253399203467448706 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 828760197610402346119) ^ 6049344508105126614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 828760197610402346119) ^ 822 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1190926127182048880113 : Nat.Prime 1190926127182048880113 := by
  apply lucas_primality 1190926127182048880113 (5 : ZMod 1190926127182048880113)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (1231, 1), (959767938685519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (1231, 1), (959767938685519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190926127182048880113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_1231
      · exact prime_sixtyTwoBH_959767938685519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1190926127182048880113) ^ 595463063591024440056 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190926127182048880113) ^ 396975375727349626704 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190926127182048880113) ^ 170132303883149840016 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190926127182048880113) ^ 967446082195003152 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1190926127182048880113) ^ 1240848 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1204381266710048956759 : Nat.Prime 1204381266710048956759 := by
  apply lucas_primality 1204381266710048956759 (15 : ZMod 1204381266710048956759)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23173441, 1), (8662080487673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23173441, 1), (8662080487673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1204381266710048956759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_23173441
      · exact prime_sixtyTwoBH_8662080487673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 1204381266710048956759) ^ 602190633355024478379 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1204381266710048956759) ^ 401460422236682985586 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1204381266710048956759) ^ 51972482926038 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1204381266710048956759) ^ 139040646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1356480607419989455907 : Nat.Prime 1356480607419989455907 := by
  apply lucas_primality 1356480607419989455907 (2 : ZMod 1356480607419989455907)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (283, 1), (16067, 1), (48869, 1), (13328873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (283, 1), (16067, 1), (48869, 1), (13328873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1356480607419989455907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_229
      · exact prime_sixtyTwoBH_283
      · exact prime_sixtyTwoBH_16067
      · exact prime_sixtyTwoBH_48869
      · exact prime_sixtyTwoBH_13328873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1356480607419989455907) ^ 678240303709994727953 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356480607419989455907) ^ 5923496102270696314 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356480607419989455907) ^ 4793217694063566982 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356480607419989455907) ^ 84426501986680118 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356480607419989455907) ^ 27757486492868474 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356480607419989455907) ^ 101770090195922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1573156518749814358951 : Nat.Prime 1573156518749814358951 := by
  apply lucas_primality 1573156518749814358951 (3 : ZMod 1573156518749814358951)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (36590497, 1), (286623877369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (36590497, 1), (286623877369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1573156518749814358951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_36590497
      · exact prime_sixtyTwoBH_286623877369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1573156518749814358951) ^ 786578259374907179475 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1573156518749814358951) ^ 524385506249938119650 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1573156518749814358951) ^ 314631303749962871790 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1573156518749814358951) ^ 42993581605350 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1573156518749814358951) ^ 5488574550 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2049285273461519822653 : Nat.Prime 2049285273461519822653 := by
  apply lucas_primality 2049285273461519822653 (6 : ZMod 2049285273461519822653)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (53, 1), (9833, 1), (4255675833677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (53, 1), (9833, 1), (4255675833677, 1)] : List FactorBlock).map factorBlockValue).prod) = 2049285273461519822653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_53
      · exact prime_sixtyTwoBH_9833
      · exact prime_sixtyTwoBH_4255675833677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2049285273461519822653) ^ 1024642636730759911326 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 683095091153839940884 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 292755039065931403236 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 186298661223774529332 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 38665759876632449484 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 208408956926830044 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2049285273461519822653) ^ 481541676 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2330614678800450838171 : Nat.Prime 2330614678800450838171 := by
  apply lucas_primality 2330614678800450838171 (2 : ZMod 2330614678800450838171)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (77687155960015027939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (77687155960015027939, 1)] : List FactorBlock).map factorBlockValue).prod) = 2330614678800450838171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_77687155960015027939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2330614678800450838171) ^ 1165307339400225419085 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2330614678800450838171) ^ 776871559600150279390 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2330614678800450838171) ^ 466122935760090167634 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2330614678800450838171) ^ 30 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3097495012114156899659 : Nat.Prime 3097495012114156899659 := by
  apply lucas_primality 3097495012114156899659 (2 : ZMod 3097495012114156899659)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (151, 1), (199, 1), (37507, 1), (196309007729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (151, 1), (199, 1), (37507, 1), (196309007729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3097495012114156899659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_199
      · exact prime_sixtyTwoBH_37507
      · exact prime_sixtyTwoBH_196309007729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3097495012114156899659) ^ 1548747506057078449829 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097495012114156899659) ^ 442499287444879557094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097495012114156899659) ^ 20513212000756005958 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097495012114156899659) ^ 15565301568412848742 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097495012114156899659) ^ 82584451225482094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097495012114156899659) ^ 15778669802 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_3722888851538241573647 : Nat.Prime 3722888851538241573647 := by
  apply lucas_primality 3722888851538241573647 (5 : ZMod 3722888851538241573647)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (43289405250444669461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (43289405250444669461, 1)] : List FactorBlock).map factorBlockValue).prod) = 3722888851538241573647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_43
      · exact prime_sixtyTwoBH_43289405250444669461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3722888851538241573647) ^ 1861444425769120786823 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3722888851538241573647) ^ 86578810500889338922 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3722888851538241573647) ^ 86 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_24114354090288659951227 : Nat.Prime 24114354090288659951227 := by
  apply lucas_primality 24114354090288659951227 (2 : ZMod 24114354090288659951227)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (2293, 1), (43781, 1), (351347, 1), (941701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (2293, 1), (43781, 1), (351347, 1), (941701, 1)] : List FactorBlock).map factorBlockValue).prod) = 24114354090288659951227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_2293
      · exact prime_sixtyTwoBH_43781
      · exact prime_sixtyTwoBH_351347
      · exact prime_sixtyTwoBH_941701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24114354090288659951227) ^ 12057177045144329975613 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 8038118030096219983742 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 2192214008208059995566 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 10516508543518822482 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 550794958778663346 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 68634011647427358 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24114354090288659951227) ^ 25607229991567026 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_26099006291976620515697 : Nat.Prime 26099006291976620515697 := by
  apply lucas_primality 26099006291976620515697 (3 : ZMod 26099006291976620515697)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (51869, 1), (31448223278808899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (51869, 1), (31448223278808899, 1)] : List FactorBlock).map factorBlockValue).prod) = 26099006291976620515697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_51869
      · exact prime_sixtyTwoBH_31448223278808899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26099006291976620515697) ^ 13049503145988310257848 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26099006291976620515697) ^ 503171572460942384 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26099006291976620515697) ^ 829904 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_364200983853918144256819 : Nat.Prime 364200983853918144256819 := by
  apply lucas_primality 364200983853918144256819 (10 : ZMod 364200983853918144256819)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (402343, 1), (27646081, 1), (55121959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (402343, 1), (27646081, 1), (55121959, 1)] : List FactorBlock).map factorBlockValue).prod) = 364200983853918144256819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_11
      · exact prime_sixtyTwoBH_402343
      · exact prime_sixtyTwoBH_27646081
      · exact prime_sixtyTwoBH_55121959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 364200983853918144256819) ^ 182100491926959072128409 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 364200983853918144256819) ^ 121400327951306048085606 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 364200983853918144256819) ^ 33109180350356194932438 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 364200983853918144256819) ^ 905200249175251326 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 364200983853918144256819) ^ 13173693003862578 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 364200983853918144256819) ^ 6607185057663102 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_432298577579470284180847 : Nat.Prime 432298577579470284180847 := by
  apply lucas_primality 432298577579470284180847 (3 : ZMod 432298577579470284180847)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1031, 1), (1181, 1), (36268619, 1), (1631522149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1031, 1), (1181, 1), (36268619, 1), (1631522149, 1)] : List FactorBlock).map factorBlockValue).prod) = 432298577579470284180847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_1031
      · exact prime_sixtyTwoBH_1181
      · exact prime_sixtyTwoBH_36268619
      · exact prime_sixtyTwoBH_1631522149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 432298577579470284180847) ^ 216149288789735142090423 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 432298577579470284180847) ^ 144099525859823428060282 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 432298577579470284180847) ^ 419300269233239848866 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 432298577579470284180847) ^ 366044519542311840966 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 432298577579470284180847) ^ 11919355892196234 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 432298577579470284180847) ^ 264966416695254 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_583538035683721411512287 : Nat.Prime 583538035683721411512287 := by
  apply lucas_primality 583538035683721411512287 (5 : ZMod 583538035683721411512287)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (157, 1), (1613, 1), (10767661045638389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (157, 1), (1613, 1), (10767661045638389, 1)] : List FactorBlock).map factorBlockValue).prod) = 583538035683721411512287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_107
      · exact prime_sixtyTwoBH_157
      · exact prime_sixtyTwoBH_1613
      · exact prime_sixtyTwoBH_10767661045638389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 583538035683721411512287) ^ 291769017841860705756143 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 583538035683721411512287) ^ 5453626501717022537498 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 583538035683721411512287) ^ 3716802775055550391798 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 583538035683721411512287) ^ 361771875811358593622 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 583538035683721411512287) ^ 54193574 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_719345104607257984727077 : Nat.Prime 719345104607257984727077 := by
  apply lucas_primality 719345104607257984727077 (2 : ZMod 719345104607257984727077)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (151, 1), (20894188004161089367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (151, 1), (20894188004161089367, 1)] : List FactorBlock).map factorBlockValue).prod) = 719345104607257984727077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_151
      · exact prime_sixtyTwoBH_20894188004161089367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 719345104607257984727077) ^ 359672552303628992363538 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 719345104607257984727077) ^ 239781701535752661575692 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 719345104607257984727077) ^ 37860268663539893933004 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 719345104607257984727077) ^ 4763874864948728375676 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 719345104607257984727077) ^ 34428 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1100823686521017336502687 : Nat.Prime 1100823686521017336502687 := by
  apply lucas_primality 1100823686521017336502687 (3 : ZMod 1100823686521017336502687)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (189361, 1), (27974981, 1), (3848253449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (189361, 1), (27974981, 1), (3848253449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100823686521017336502687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_189361
      · exact prime_sixtyTwoBH_27974981
      · exact prime_sixtyTwoBH_3848253449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1100823686521017336502687) ^ 550411843260508668251343 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100823686521017336502687) ^ 366941228840339112167562 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100823686521017336502687) ^ 5813360124423811326 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100823686521017336502687) ^ 39350292553228806 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100823686521017336502687) ^ 286058000365614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1379022214967358644423833 : Nat.Prime 1379022214967358644423833 := by
  apply lucas_primality 1379022214967358644423833 (5 : ZMod 1379022214967358644423833)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (269, 1), (10601, 1), (221421359946967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (269, 1), (10601, 1), (221421359946967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1379022214967358644423833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_269
      · exact prime_sixtyTwoBH_10601
      · exact prime_sixtyTwoBH_221421359946967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1379022214967358644423833) ^ 689511107483679322211916 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 459674071655786214807944 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 197003173566765520631976 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 106078631920566049571064 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 5126476635566389012728 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 130084163283403324632 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1379022214967358644423833) ^ 6228045096 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_5181715454147814321059269 : Nat.Prime 5181715454147814321059269 := by
  apply lucas_primality 5181715454147814321059269 (2 : ZMod 5181715454147814321059269)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (113, 1), (7877, 1), (37317253554457003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (113, 1), (7877, 1), (37317253554457003, 1)] : List FactorBlock).map factorBlockValue).prod) = 5181715454147814321059269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_13
      · exact prime_sixtyTwoBH_113
      · exact prime_sixtyTwoBH_7877
      · exact prime_sixtyTwoBH_37317253554457003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5181715454147814321059269) ^ 2590857727073907160529634 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5181715454147814321059269) ^ 1727238484715938107019756 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5181715454147814321059269) ^ 398593496472908793927636 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5181715454147814321059269) ^ 45855888974759418770436 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5181715454147814321059269) ^ 657828545657968048884 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5181715454147814321059269) ^ 138855756 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9016057418742310133542979 : Nat.Prime 9016057418742310133542979 := by
  apply lucas_primality 9016057418742310133542979 (6 : ZMod 9016057418742310133542979)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (271, 1), (581491, 1), (426972183358247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (271, 1), (581491, 1), (426972183358247, 1)] : List FactorBlock).map factorBlockValue).prod) = 9016057418742310133542979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_67
      · exact prime_sixtyTwoBH_271
      · exact prime_sixtyTwoBH_581491
      · exact prime_sixtyTwoBH_426972183358247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9016057418742310133542979) ^ 4508028709371155066771489 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9016057418742310133542979) ^ 134568021175258360202134 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9016057418742310133542979) ^ 33269584571004834441118 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9016057418742310133542979) ^ 15505067866471381558 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 9016057418742310133542979) ^ 21116264174 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_11561600443907725770615839 : Nat.Prime 11561600443907725770615839 := by
  apply lucas_primality 11561600443907725770615839 (37 : ZMod 11561600443907725770615839)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (139, 1), (90071, 1), (3653467, 1), (256351621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (139, 1), (90071, 1), (3653467, 1), (256351621, 1)] : List FactorBlock).map factorBlockValue).prod) = 11561600443907725770615839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_17
      · exact prime_sixtyTwoBH_29
      · exact prime_sixtyTwoBH_139
      · exact prime_sixtyTwoBH_90071
      · exact prime_sixtyTwoBH_3653467
      · exact prime_sixtyTwoBH_256351621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 11561600443907725770615839) ^ 5780800221953862885307919 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 680094143759277986506814 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 398675877376128474848822 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 83176981610846947990042 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 128360964615777839378 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 3164555870877641914 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (37 : ZMod 11561600443907725770615839) ^ 45100555240521478 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_12914120298515676776903527 : Nat.Prime 12914120298515676776903527 := by
  apply lucas_primality 12914120298515676776903527 (3 : ZMod 12914120298515676776903527)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8009, 1), (186707, 1), (1439377411225267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8009, 1), (186707, 1), (1439377411225267, 1)] : List FactorBlock).map factorBlockValue).prod) = 12914120298515676776903527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_8009
      · exact prime_sixtyTwoBH_186707
      · exact prime_sixtyTwoBH_1439377411225267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12914120298515676776903527) ^ 6457060149257838388451763 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12914120298515676776903527) ^ 4304706766171892258967842 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12914120298515676776903527) ^ 1612451029905815554614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12914120298515676776903527) ^ 69167842119018980418 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12914120298515676776903527) ^ 8972018178 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_13969991769463499406461677 : Nat.Prime 13969991769463499406461677 := by
  apply lucas_primality 13969991769463499406461677 (2 : ZMod 13969991769463499406461677)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (359, 1), (34843, 1), (31022990508841343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (359, 1), (34843, 1), (31022990508841343, 1)] : List FactorBlock).map factorBlockValue).prod) = 13969991769463499406461677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_359
      · exact prime_sixtyTwoBH_34843
      · exact prime_sixtyTwoBH_31022990508841343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13969991769463499406461677) ^ 6984995884731749703230838 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969991769463499406461677) ^ 4656663923154499802153892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969991769463499406461677) ^ 38913626098784120909364 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969991769463499406461677) ^ 400941129336265516932 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13969991769463499406461677) ^ 450310932 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_23915349694738982507570773 : Nat.Prime 23915349694738982507570773 := by
  apply lucas_primality 23915349694738982507570773 (2 : ZMod 23915349694738982507570773)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (131, 1), (3691, 1), (111398264425694203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (131, 1), (3691, 1), (111398264425694203, 1)] : List FactorBlock).map factorBlockValue).prod) = 23915349694738982507570773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_131
      · exact prime_sixtyTwoBH_3691
      · exact prime_sixtyTwoBH_111398264425694203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23915349694738982507570773) ^ 11957674847369491253785386 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23915349694738982507570773) ^ 7971783231579660835856924 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23915349694738982507570773) ^ 646360802560513040745156 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23915349694738982507570773) ^ 182559921333885362653212 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23915349694738982507570773) ^ 6479368652056077623292 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23915349694738982507570773) ^ 214683324 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_38906871982152325576276231 : Nat.Prime 38906871982152325576276231 := by
  apply lucas_primality 38906871982152325576276231 (6 : ZMod 38906871982152325576276231)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (432298577579470284180847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (432298577579470284180847, 1)] : List FactorBlock).map factorBlockValue).prod) = 38906871982152325576276231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_432298577579470284180847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38906871982152325576276231) ^ 19453435991076162788138115 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 38906871982152325576276231) ^ 12968957327384108525425410 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 38906871982152325576276231) ^ 7781374396430465115255246 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (6 : ZMod 38906871982152325576276231) ^ 90 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_41530054852337099935243297 : Nat.Prime 41530054852337099935243297 := by
  apply lucas_primality 41530054852337099935243297 (7 : ZMod 41530054852337099935243297)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (8573, 1), (1630351883, 1), (30951171989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (8573, 1), (1630351883, 1), (30951171989, 1)] : List FactorBlock).map factorBlockValue).prod) = 41530054852337099935243297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_8573
      · exact prime_sixtyTwoBH_1630351883
      · exact prime_sixtyTwoBH_30951171989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 41530054852337099935243297) ^ 20765027426168549967621648 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 41530054852337099935243297) ^ 13843351617445699978414432 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 41530054852337099935243297) ^ 4844284947199008507552 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 41530054852337099935243297) ^ 25473062156322912 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (7 : ZMod 41530054852337099935243297) ^ 1341792642524064 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_95195515343344131669745999 : Nat.Prime 95195515343344131669745999 := by
  apply lucas_primality 95195515343344131669745999 (3 : ZMod 95195515343344131669745999)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (479, 1), (704744779633575650141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (479, 1), (704744779633575650141, 1)] : List FactorBlock).map factorBlockValue).prod) = 95195515343344131669745999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_47
      · exact prime_sixtyTwoBH_479
      · exact prime_sixtyTwoBH_704744779633575650141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95195515343344131669745999) ^ 47597757671672065834872999 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 95195515343344131669745999) ^ 31731838447781377223248666 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 95195515343344131669745999) ^ 2025436496666896418505234 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 95195515343344131669745999) ^ 198738027856668333339762 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 95195515343344131669745999) ^ 135078 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_113468338721942695643505293 : Nat.Prime 113468338721942695643505293 := by
  apply lucas_primality 113468338721942695643505293 (2 : ZMod 113468338721942695643505293)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (349, 1), (613, 1), (132595505595038136979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (349, 1), (613, 1), (132595505595038136979, 1)] : List FactorBlock).map factorBlockValue).prod) = 113468338721942695643505293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_349
      · exact prime_sixtyTwoBH_613
      · exact prime_sixtyTwoBH_132595505595038136979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113468338721942695643505293) ^ 56734169360971347821752646 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113468338721942695643505293) ^ 325124179719033511872508 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113468338721942695643505293) ^ 185103325810673239222684 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113468338721942695643505293) ^ 855748 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_161811361621136824251003133 : Nat.Prime 161811361621136824251003133 := by
  apply lucas_primality 161811361621136824251003133 (2 : ZMod 161811361621136824251003133)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (257, 1), (540251, 1), (2453467, 1), (807835181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (257, 1), (540251, 1), (2453467, 1), (807835181, 1)] : List FactorBlock).map factorBlockValue).prod) = 161811361621136824251003133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_257
      · exact prime_sixtyTwoBH_540251
      · exact prime_sixtyTwoBH_2453467
      · exact prime_sixtyTwoBH_807835181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161811361621136824251003133) ^ 80905680810568412125501566 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 53937120540378941417001044 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 23115908803019546321571876 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 629616193078353401754876 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 299511452308532190132 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 65952124736602050996 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161811361621136824251003133) ^ 200302444640792172 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_394088961367607426804862469 : Nat.Prime 394088961367607426804862469 := by
  apply lucas_primality 394088961367607426804862469 (2 : ZMod 394088961367607426804862469)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (191, 1), (311, 1), (2703369671, 1), (9738555329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (191, 1), (311, 1), (2703369671, 1), (9738555329, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607426804862469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_191
      · exact prime_sixtyTwoBH_311
      · exact prime_sixtyTwoBH_2703369671
      · exact prime_sixtyTwoBH_9738555329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 394088961367607426804862469) ^ 197044480683803713402431234 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 131362987122535808934954156 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 56298423052515346686408924 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 2063292991453442025156348 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 1267167078352435455964188 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 145776941124678108 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 394088961367607426804862469) ^ 40466881180421892 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_648677405436946737926587781 : Nat.Prime 648677405436946737926587781 := by
  apply lucas_primality 648677405436946737926587781 (2 : ZMod 648677405436946737926587781)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (283, 1), (3097495012114156899659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (283, 1), (3097495012114156899659, 1)] : List FactorBlock).map factorBlockValue).prod) = 648677405436946737926587781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_37
      · exact prime_sixtyTwoBH_283
      · exact prime_sixtyTwoBH_3097495012114156899659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 648677405436946737926587781) ^ 324338702718473368963293890 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 648677405436946737926587781) ^ 129735481087389347585317556 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 648677405436946737926587781) ^ 17531821768566128052069940 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 648677405436946737926587781) ^ 2292146308964476105747660 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 648677405436946737926587781) ^ 209420 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_1285974505515350550626393321 : Nat.Prime 1285974505515350550626393321 := by
  apply lucas_primality 1285974505515350550626393321 (3 : ZMod 1285974505515350550626393321)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (757, 1), (35323, 1), (912559, 1), (69343275643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (757, 1), (35323, 1), (912559, 1), (69343275643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1285974505515350550626393321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_5
      · exact prime_sixtyTwoBH_19
      · exact prime_sixtyTwoBH_757
      · exact prime_sixtyTwoBH_35323
      · exact prime_sixtyTwoBH_912559
      · exact prime_sixtyTwoBH_69343275643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1285974505515350550626393321) ^ 642987252757675275313196660 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 257194901103070110125278664 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 67682868711334239506652280 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 1698777418118032431474760 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 36406151955251551414840 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 1409196014192343235480 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1285974505515350550626393321) ^ 18545049878173240 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_2527605062564654530541531699 : Nat.Prime 2527605062564654530541531699 := by
  apply lucas_primality 2527605062564654530541531699 (2 : ZMod 2527605062564654530541531699)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379695853, 1), (3328460190694595933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379695853, 1), (3328460190694595933, 1)] : List FactorBlock).map factorBlockValue).prod) = 2527605062564654530541531699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_379695853
      · exact prime_sixtyTwoBH_3328460190694595933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2527605062564654530541531699) ^ 1263802531282327265270765849 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2527605062564654530541531699) ^ 6656920381389191866 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2527605062564654530541531699) ^ 759391706 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_6108378901197915115475368273 : Nat.Prime 6108378901197915115475368273 := by
  apply lucas_primality 6108378901197915115475368273 (10 : ZMod 6108378901197915115475368273)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (467, 1), (1993, 1), (319511, 1), (142643991397393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (467, 1), (1993, 1), (319511, 1), (142643991397393, 1)] : List FactorBlock).map factorBlockValue).prod) = 6108378901197915115475368273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_467
      · exact prime_sixtyTwoBH_1993
      · exact prime_sixtyTwoBH_319511
      · exact prime_sixtyTwoBH_142643991397393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6108378901197915115475368273) ^ 3054189450598957557737684136 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 6108378901197915115475368273) ^ 2036126300399305038491789424 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 6108378901197915115475368273) ^ 13080040473657205814722416 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 6108378901197915115475368273) ^ 3064916658905125496977104 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 6108378901197915115475368273) ^ 19117898605049325736752 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (10 : ZMod 6108378901197915115475368273) ^ 42822546125904 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_9162568351796872673213052407 : Nat.Prime 9162568351796872673213052407 := by
  apply lucas_primality 9162568351796872673213052407 (5 : ZMod 9162568351796872673213052407)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1091, 1), (493121, 1), (1189758041, 1), (7157318353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1091, 1), (493121, 1), (1189758041, 1), (7157318353, 1)] : List FactorBlock).map factorBlockValue).prod) = 9162568351796872673213052407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_1091
      · exact prime_sixtyTwoBH_493121
      · exact prime_sixtyTwoBH_1189758041
      · exact prime_sixtyTwoBH_7157318353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9162568351796872673213052407) ^ 4581284175898436336606526203 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9162568351796872673213052407) ^ 8398321129053045529984466 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9162568351796872673213052407) ^ 18580770950328362964086 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9162568351796872673213052407) ^ 7701203132105473766 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9162568351796872673213052407) ^ 1280167780710266902 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_10471506687767854483672059899 : Nat.Prime 10471506687767854483672059899 := by
  apply lucas_primality 10471506687767854483672059899 (2 : ZMod 10471506687767854483672059899)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (193, 1), (2857, 1), (1356480607419989455907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (193, 1), (2857, 1), (1356480607419989455907, 1)] : List FactorBlock).map factorBlockValue).prod) = 10471506687767854483672059899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_7
      · exact prime_sixtyTwoBH_193
      · exact prime_sixtyTwoBH_2857
      · exact prime_sixtyTwoBH_1356480607419989455907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10471506687767854483672059899) ^ 5235753343883927241836029949 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471506687767854483672059899) ^ 1495929526823979211953151414 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471506687767854483672059899) ^ 54256511335584738257368186 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471506687767854483672059899) ^ 3665210601248811509860714 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10471506687767854483672059899) ^ 7719614 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_24433515604791660461901473089 : Nat.Prime 24433515604791660461901473089 := by
  apply lucas_primality 24433515604791660461901473089 (13 : ZMod 24433515604791660461901473089)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (467, 1), (1993, 1), (319511, 1), (142643991397393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (467, 1), (1993, 1), (319511, 1), (142643991397393, 1)] : List FactorBlock).map factorBlockValue).prod) = 24433515604791660461901473089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_467
      · exact prime_sixtyTwoBH_1993
      · exact prime_sixtyTwoBH_319511
      · exact prime_sixtyTwoBH_142643991397393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24433515604791660461901473089) ^ 12216757802395830230950736544 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791660461901473089) ^ 8144505201597220153967157696 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791660461901473089) ^ 52320161894628823258889664 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791660461901473089) ^ 12259666635620501987908416 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791660461901473089) ^ 76471594420197302947008 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791660461901473089) ^ 171290184503616 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem prime_sixtyTwoBH_73300546814374981385704419283 : Nat.Prime 73300546814374981385704419283 := by
  apply lucas_primality 73300546814374981385704419283 (2 : ZMod 73300546814374981385704419283)
  · rw [← sixtyTwoBHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2953, 1), (1379022214967358644423833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2953, 1), (1379022214967358644423833, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyTwoBH_2
      · exact prime_sixtyTwoBH_3
      · exact prime_sixtyTwoBH_2953
      · exact prime_sixtyTwoBH_1379022214967358644423833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73300546814374981385704419283) ^ 36650273407187490692852209641 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73300546814374981385704419283) ^ 24433515604791660461901473094 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73300546814374981385704419283) ^ 24822399869412455599628994 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73300546814374981385704419283) ^ 53154 ≠ 1
      rw [← sixtyTwoBHFastPow_eq_pow]
      decide

private theorem phi_sixtyTwoBH_73300546814374981385704419200 : Nat.totient 73300546814374981385704419200 = 29319627174685370425746432000 := by
  rw [← show ((([(2, 7), (5, 2), (85717, 1), (185051, 1), (322039, 1), (4484255687, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_85717, prime_sixtyTwoBH_185051, prime_sixtyTwoBH_322039, prime_sixtyTwoBH_4484255687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419201 : Nat.totient 73300546814374981385704419201 = 48641532681206970231169876992 := by
  rw [← show ((([(3, 2), (313, 1), (709, 1), (72613, 1), (194447167, 1), (2599310327, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_313, prime_sixtyTwoBH_709, prime_sixtyTwoBH_72613, prime_sixtyTwoBH_194447167, prime_sixtyTwoBH_2599310327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419202 : Nat.totient 73300546814374981385704419202 = 29035243190707407588035589120 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (41, 1), (2410761589673, 1), (2787965901629, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_7, prime_sixtyTwoBH_19, prime_sixtyTwoBH_41, prime_sixtyTwoBH_2410761589673, prime_sixtyTwoBH_2787965901629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419203 : Nat.totient 73300546814374981385704419203 = 70935677282172943286778251520 := by
  rw [← show ((([(31, 1), (445853, 1), (735983, 1), (883703, 1), (8154169129, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_31, prime_sixtyTwoBH_445853, prime_sixtyTwoBH_735983, prime_sixtyTwoBH_883703, prime_sixtyTwoBH_8154169129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419204 : Nat.totient 73300546814374981385704419204 = 24277888116863051159596367520 := by
  rw [← show ((([(2, 2), (3, 1), (157, 1), (38906871982152325576276231, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_157, prime_sixtyTwoBH_38906871982152325576276231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419205 : Nat.totient 73300546814374981385704419205 = 58474317232090636708822560768 := by
  rw [← show ((([(5, 1), (353, 1), (41530054852337099935243297, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_353, prime_sixtyTwoBH_41530054852337099935243297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419206 : Nat.totient 73300546814374981385704419206 = 36009335194788679243773327360 := by
  rw [← show ((([(2, 1), (59, 1), (3581, 1), (3719, 1), (43781707, 1), (1065373812929, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_59, prime_sixtyTwoBH_3581, prime_sixtyTwoBH_3719, prime_sixtyTwoBH_43781707, prime_sixtyTwoBH_1065373812929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419207 : Nat.totient 73300546814374981385704419207 = 44641806287134583073484062720 := by
  rw [← show ((([(3, 1), (13, 1), (97, 1), (61781, 1), (96997, 1), (5328023, 1), (606864239, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_13, prime_sixtyTwoBH_97, prime_sixtyTwoBH_61781, prime_sixtyTwoBH_96997, prime_sixtyTwoBH_5328023, prime_sixtyTwoBH_606864239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419208 : Nat.totient 73300546814374981385704419208 = 31869027069687423613955358720 := by
  rw [← show ((([(2, 3), (11, 1), (23, 1), (41177, 1), (16580269, 1), (53045730141409, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_11, prime_sixtyTwoBH_23, prime_sixtyTwoBH_41177, prime_sixtyTwoBH_16580269, prime_sixtyTwoBH_53045730141409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419209 : Nat.totient 73300546814374981385704419209 = 61347677761096490842698739392 := by
  rw [← show ((([(7, 1), (43, 1), (4327, 1), (10159, 1), (5539911964211798213, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_7, prime_sixtyTwoBH_43, prime_sixtyTwoBH_4327, prime_sixtyTwoBH_10159, prime_sixtyTwoBH_5539911964211798213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419210 : Nat.totient 73300546814374981385704419210 = 18396999925280403898778376192 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (17, 1), (309172987, 1), (51652695137778937, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_17, prime_sixtyTwoBH_309172987, prime_sixtyTwoBH_51652695137778937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419211 : Nat.totient 73300546814374981385704419211 = 72722510272696707174391758720 := by
  rw [← show ((([(127, 1), (83891, 1), (37073450599, 1), (185577411377, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_127, prime_sixtyTwoBH_83891, prime_sixtyTwoBH_37073450599, prime_sixtyTwoBH_185577411377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419212 : Nat.totient 73300546814374981385704419212 = 35831015974863781115710801920 := by
  rw [← show ((([(2, 2), (47, 1), (1097, 1), (5297, 1), (67098492758646439861, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_47, prime_sixtyTwoBH_1097, prime_sixtyTwoBH_5297, prime_sixtyTwoBH_67098492758646439861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419213 : Nat.totient 73300546814374981385704419213 = 47181914757302485054186944960 := by
  rw [← show ((([(3, 1), (29, 1), (1016621, 1), (828760197610402346119, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_29, prime_sixtyTwoBH_1016621, prime_sixtyTwoBH_828760197610402346119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419214 : Nat.totient 73300546814374981385704419214 = 35659725432642157645917603072 := by
  rw [← show ((([(2, 1), (37, 1), (799162913, 1), (1239481855089521947, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_37, prime_sixtyTwoBH_799162913, prime_sixtyTwoBH_1239481855089521947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419215 : Nat.totient 73300546814374981385704419215 = 58590534329997509855191478400 := by
  rw [← show ((([(5, 1), (1741, 1), (3613, 1), (2330614678800450838171, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_1741, prime_sixtyTwoBH_3613, prime_sixtyTwoBH_2330614678800450838171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419216 : Nat.totient 73300546814374981385704419216 = 20908050081085732825495407744 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (599, 1), (364200983853918144256819, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_7, prime_sixtyTwoBH_599, prime_sixtyTwoBH_364200983853918144256819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419217 : Nat.totient 73300546814374981385704419217 = 73300545241218462635843465700 := by
  rw [← show ((([(46594567, 1), (1573156518749814358951, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_46594567, prime_sixtyTwoBH_1573156518749814358951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419218 : Nat.totient 73300546814374981385704419218 = 36342748862382169508985172080 := by
  rw [← show ((([(2, 1), (181, 1), (347, 1), (583538035683721411512287, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_181, prime_sixtyTwoBH_347, prime_sixtyTwoBH_583538035683721411512287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419219 : Nat.totient 73300546814374981385704419219 = 43586374320726118148160429120 := by
  rw [← show ((([(3, 2), (11, 1), (53, 1), (13969991769463499406461677, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_11, prime_sixtyTwoBH_53, prime_sixtyTwoBH_13969991769463499406461677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419220 : Nat.totient 73300546814374981385704419220 = 27064701664706081269999310976 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (234083, 1), (1204381266710048956759, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_13, prime_sixtyTwoBH_234083, prime_sixtyTwoBH_1204381266710048956759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419221 : Nat.totient 73300546814374981385704419221 = 69440821590557641714360915968 := by
  rw [← show ((([(19, 1), (38543, 1), (4615091137, 1), (21688415101849, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_19, prime_sixtyTwoBH_38543, prime_sixtyTwoBH_4615091137, prime_sixtyTwoBH_21688415101849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419222 : Nat.totient 73300546814374981385704419222 = 24205164988009502053680344864 := by
  rw [← show ((([(2, 1), (3, 1), (107, 1), (6625628957, 1), (17232372549902663, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_107, prime_sixtyTwoBH_6625628957, prime_sixtyTwoBH_17232372549902663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419223 : Nat.totient 73300546814374981385704419223 = 62824724055979483354123909536 := by
  rw [← show ((([(7, 1), (14557, 1), (719345104607257984727077, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_7, prime_sixtyTwoBH_14557, prime_sixtyTwoBH_719345104607257984727077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419224 : Nat.totient 73300546814374981385704419224 = 36645170965817143337705697024 := by
  rw [← show ((([(2, 3), (7577, 1), (138077, 1), (8757872083560501607, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_7577, prime_sixtyTwoBH_138077, prime_sixtyTwoBH_8757872083560501607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419225 : Nat.totient 73300546814374981385704419225 = 39093624926070844334364750720 := by
  rw [← show ((([(3, 1), (5, 2), (939845209, 1), (1039895309177094947, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_939845209, prime_sixtyTwoBH_1039895309177094947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419226 : Nat.totient 73300546814374981385704419226 = 36403747430327479874077100560 := by
  rw [← show ((([(2, 1), (149, 1), (66071, 1), (3722888851538241573647, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_149, prime_sixtyTwoBH_66071, prime_sixtyTwoBH_3722888851538241573647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419227 : Nat.totient 73300546814374981385704419227 = 68988749942935948359442282624 := by
  rw [← show ((([(17, 1), (13827182852759, 1), (311834805205709, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_17, prime_sixtyTwoBH_13827182852759, prime_sixtyTwoBH_311834805205709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419228 : Nat.totient 73300546814374981385704419228 = 24433515604729718598880501056 := by
  rw [← show ((([(2, 2), (3, 2), (394488991319, 1), (5161427429423017, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_394488991319, prime_sixtyTwoBH_5161427429423017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419229 : Nat.totient 73300546814374981385704419229 = 73114695790569815871009339456 := by
  rw [← show ((([(419, 1), (6703, 1), (26099006291976620515697, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_419, prime_sixtyTwoBH_6703, prime_sixtyTwoBH_26099006291976620515697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419230 : Nat.totient 73300546814374981385704419230 = 22846923682402591600739039520 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (11, 1), (95195515343344131669745999, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_7, prime_sixtyTwoBH_11, prime_sixtyTwoBH_95195515343344131669745999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419231 : Nat.totient 73300546814374981385704419231 = 46706931638759104117048300800 := by
  rw [← show ((([(3, 1), (23, 1), (1319, 1), (5810201, 1), (275953003, 1), (502327607, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_23, prime_sixtyTwoBH_1319, prime_sixtyTwoBH_5810201, prime_sixtyTwoBH_275953003, prime_sixtyTwoBH_502327607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419232 : Nat.totient 73300546814374981385704419232 = 36650273407164446758657162752 := by
  rw [← show ((([(2, 5), (1592212307897, 1), (1438653674882533, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_1592212307897, prime_sixtyTwoBH_1438653674882533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419233 : Nat.totient 73300546814374981385704419233 = 67645022933338431809375557440 := by
  rw [← show ((([(13, 1), (4919, 1), (20719, 1), (55324595736571414381, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_13, prime_sixtyTwoBH_4919, prime_sixtyTwoBH_20719, prime_sixtyTwoBH_55324595736571414381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419234 : Nat.totient 73300546814374981385704419234 = 23645337682056445608291748080 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (394088961367607426804862469, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_31, prime_sixtyTwoBH_394088961367607426804862469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419235 : Nat.totient 73300546814374981385704419235 = 58071112815532760588588846688 := by
  rw [← show ((([(5, 1), (103, 1), (112601491447, 1), (1264025520744167, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_103, prime_sixtyTwoBH_112601491447, prime_sixtyTwoBH_1264025520744167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419236 : Nat.totient 73300546814374981385704419236 = 36105081421250432092236134400 := by
  rw [← show ((([(2, 2), (79, 1), (463, 1), (11617, 1), (43126593119693132201, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_79, prime_sixtyTwoBH_463, prime_sixtyTwoBH_11617, prime_sixtyTwoBH_43126593119693132201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419237 : Nat.totient 73300546814374981385704419237 = 41884901470235410301998267488 := by
  rw [← show ((([(3, 5), (7, 2), (37223, 1), (6475622003, 1), (25539476939, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_7, prime_sixtyTwoBH_37223, prime_sixtyTwoBH_6475622003, prime_sixtyTwoBH_25539476939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419238 : Nat.totient 73300546814374981385704419238 = 35988967888242526198322288640 := by
  rw [← show ((([(2, 1), (73, 1), (227, 1), (9618041, 1), (229954481290187729, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_73, prime_sixtyTwoBH_227, prime_sixtyTwoBH_9618041, prime_sixtyTwoBH_229954481290187729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419239 : Nat.totient 73300546814374981385704419239 = 71540758355929725867955632000 := by
  rw [← show ((([(61, 1), (191, 1), (397, 1), (136532827, 1), (116069048104531, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_61, prime_sixtyTwoBH_191, prime_sixtyTwoBH_397, prime_sixtyTwoBH_136532827, prime_sixtyTwoBH_116069048104531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419240 : Nat.totient 73300546814374981385704419240 = 18493026663237256366321010688 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (19, 2), (757, 1), (35323, 1), (912559, 1), (69343275643, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_19, prime_sixtyTwoBH_757, prime_sixtyTwoBH_35323, prime_sixtyTwoBH_912559, prime_sixtyTwoBH_69343275643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419241 : Nat.totient 73300546814374981385704419241 = 66636857137039187817930293520 := by
  rw [← show ((([(11, 1), (19896319, 1), (262304363, 1), (1276839411823, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_11, prime_sixtyTwoBH_19896319, prime_sixtyTwoBH_262304363, prime_sixtyTwoBH_1276839411823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419242 : Nat.totient 73300546814374981385704419242 = 35386470782708278077501273792 := by
  rw [← show ((([(2, 1), (29, 1), (379695853, 1), (3328460190694595933, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_29, prime_sixtyTwoBH_379695853, prime_sixtyTwoBH_3328460190694595933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419243 : Nat.totient 73300546814374981385704419243 = 47667654884111820889371955200 := by
  rw [← show ((([(3, 1), (41, 1), (6359, 1), (195743809, 1), (478768140818711, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_41, prime_sixtyTwoBH_6359, prime_sixtyTwoBH_195743809, prime_sixtyTwoBH_478768140818711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419244 : Nat.totient 73300546814374981385704419244 = 29563772270260582101138923520 := by
  rw [← show ((([(2, 2), (7, 1), (17, 1), (15391, 1), (32353, 1), (309256520891766803, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_7, prime_sixtyTwoBH_17, prime_sixtyTwoBH_15391, prime_sixtyTwoBH_32353, prime_sixtyTwoBH_309256520891766803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419245 : Nat.totient 73300546814374981385704419245 = 58544776052721029178533249856 := by
  rw [← show ((([(5, 1), (613, 1), (23915349694738982507570773, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_613, prime_sixtyTwoBH_23915349694738982507570773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419246 : Nat.totient 73300546814374981385704419246 = 22554014288017656306916533312 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (193753997, 1), (1616741873260201927, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_13, prime_sixtyTwoBH_193753997, prime_sixtyTwoBH_1616741873260201927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419247 : Nat.totient 73300546814374981385704419247 = 72206472048741563735777015232 := by
  rw [← show ((([(67, 1), (1964617, 1), (556870887381535672573, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_67, prime_sixtyTwoBH_1964617, prime_sixtyTwoBH_556870887381535672573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419248 : Nat.totient 73300546814374981385704419248 = 36616605831818811785920512000 := by
  rw [← show ((([(2, 4), (1091, 1), (493121, 1), (1189758041, 1), (7157318353, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_1091, prime_sixtyTwoBH_493121, prime_sixtyTwoBH_1189758041, prime_sixtyTwoBH_7157318353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419249 : Nat.totient 73300546814374981385704419249 = 48543408486341047275300939600 := by
  rw [← show ((([(3, 1), (151, 1), (161811361621136824251003133, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_151, prime_sixtyTwoBH_161811361621136824251003133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419250 : Nat.totient 73300546814374981385704419250 = 29320218724424659335226009600 := by
  rw [← show ((([(2, 1), (5, 3), (22122940289, 1), (13253310067617293, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_22122940289, prime_sixtyTwoBH_13253310067617293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419251 : Nat.totient 73300546814374981385704419251 = 60246926213743465143360537600 := by
  rw [← show ((([(7, 1), (37, 1), (71, 1), (2617, 1), (27789467, 1), (54810676437581, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_7, prime_sixtyTwoBH_37, prime_sixtyTwoBH_71, prime_sixtyTwoBH_2617, prime_sixtyTwoBH_27789467, prime_sixtyTwoBH_54810676437581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419252 : Nat.totient 73300546814374981385704419252 = 21695722101506336985197923680 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (43, 1), (12914120298515676776903527, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_11, prime_sixtyTwoBH_43, prime_sixtyTwoBH_12914120298515676776903527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419253 : Nat.totient 73300546814374981385704419253 = 72651869408938034647777831360 := by
  rw [← show ((([(113, 1), (648677405436946737926587781, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_113, prime_sixtyTwoBH_648677405436946737926587781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419254 : Nat.totient 73300546814374981385704419254 = 35045510537421052527791113632 := by
  rw [← show ((([(2, 1), (23, 1), (4079, 1), (18919, 1), (42443, 1), (486509613795743, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_23, prime_sixtyTwoBH_4079, prime_sixtyTwoBH_18919, prime_sixtyTwoBH_42443, prime_sixtyTwoBH_486509613795743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419255 : Nat.totient 73300546814374981385704419255 = 38970520302719276320236929280 := by
  rw [← show ((([(3, 2), (5, 1), (373, 1), (2131, 1), (2049285273461519822653, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_373, prime_sixtyTwoBH_2131, prime_sixtyTwoBH_2049285273461519822653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419256 : Nat.totient 73300546814374981385704419256 = 36650273407187490692852209624 := by
  rw [← show ((([(2, 3), (9162568351796872673213052407, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_9162568351796872673213052407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419257 : Nat.totient 73300546814374981385704419257 = 73298610655727658332633631792 := by
  rw [← show ((([(37987, 1), (11213303, 1), (172083273954000037, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_37987, prime_sixtyTwoBH_11213303, prime_sixtyTwoBH_172083273954000037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419258 : Nat.totient 73300546814374981385704419258 = 20913796560892348495099146240 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (883, 1), (3821, 1), (872479, 1), (592877815684417, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_7, prime_sixtyTwoBH_883, prime_sixtyTwoBH_3821, prime_sixtyTwoBH_872479, prime_sixtyTwoBH_592877815684417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419259 : Nat.totient 73300546814374981385704419259 = 62737006429731469913057894400 := by
  rw [← show ((([(13, 1), (19, 1), (47, 1), (2237491, 1), (2821961641425352961, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_13, prime_sixtyTwoBH_19, prime_sixtyTwoBH_47, prime_sixtyTwoBH_2237491, prime_sixtyTwoBH_2821961641425352961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419260 : Nat.totient 73300546814374981385704419260 = 29227725922198730748116838464 := by
  rw [← show ((([(2, 2), (5, 1), (317, 1), (11561600443907725770615839, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_317, prime_sixtyTwoBH_11561600443907725770615839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419261 : Nat.totient 73300546814374981385704419261 = 45991852098147585599538078720 := by
  rw [← show ((([(3, 1), (17, 2), (70991, 1), (1190926127182048880113, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_17, prime_sixtyTwoBH_70991, prime_sixtyTwoBH_1190926127182048880113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419262 : Nat.totient 73300546814374981385704419262 = 36236350519227685844787895488 := by
  rw [← show ((([(2, 1), (89, 1), (17077, 1), (24114354090288659951227, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_89, prime_sixtyTwoBH_17077, prime_sixtyTwoBH_24114354090288659951227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419263 : Nat.totient 73300546814374981385704419263 = 66585794351393299125427166400 := by
  rw [← show ((([(11, 1), (1307, 1), (814031, 1), (6263224770566407849, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_11, prime_sixtyTwoBH_1307, prime_sixtyTwoBH_814031, prime_sixtyTwoBH_6263224770566407849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419264 : Nat.totient 73300546814374981385704419264 = 24368885758668304388179722240 := by
  rw [← show ((([(2, 6), (3, 3), (467, 1), (1993, 1), (319511, 1), (142643991397393, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_467, prime_sixtyTwoBH_1993, prime_sixtyTwoBH_319511, prime_sixtyTwoBH_142643991397393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419265 : Nat.totient 73300546814374981385704419265 = 47817399593247273119669495040 := by
  rw [← show ((([(5, 1), (7, 1), (31, 1), (59, 1), (623726951539, 1), (1835823623509, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_7, prime_sixtyTwoBH_31, prime_sixtyTwoBH_59, prime_sixtyTwoBH_623726951539, prime_sixtyTwoBH_1835823623509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419266 : Nat.totient 73300546814374981385704419266 = 36618486526200735293562229248 := by
  rw [← show ((([(2, 1), (1153, 1), (113990945639, 1), (278854434334199, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_1153, prime_sixtyTwoBH_113990945639, prime_sixtyTwoBH_278854434334199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419267 : Nat.totient 73300546814374981385704419267 = 48867031209583320923802946176 := by
  rw [← show ((([(3, 1), (24433515604791660461901473089, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_24433515604791660461901473089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419268 : Nat.totient 73300546814374981385704419268 = 36650273407186531183062773760 := by
  rw [← show ((([(2, 2), (41847012708481, 1), (437907882009457, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_41847012708481, prime_sixtyTwoBH_437907882009457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419269 : Nat.totient 73300546814374981385704419269 = 73299445990688460368367849996 := by
  rw [← show ((([(66587, 1), (1100823686521017336502687, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_66587, prime_sixtyTwoBH_1100823686521017336502687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419270 : Nat.totient 73300546814374981385704419270 = 19474684024483389888452832480 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (271, 1), (9016057418742310133542979, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_271, prime_sixtyTwoBH_9016057418742310133542979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419271 : Nat.totient 73300546814374981385704419271 = 70772941751810326855162887544 := by
  rw [← show ((([(29, 1), (2527605062564654530541531699, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_29, prime_sixtyTwoBH_2527605062564654530541531699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419272 : Nat.totient 73300546814374981385704419272 = 28210461698671175740317696000 := by
  rw [← show ((([(2, 3), (7, 1), (13, 1), (53, 1), (223, 1), (251, 1), (281797123, 1), (120443904577, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_7, prime_sixtyTwoBH_13, prime_sixtyTwoBH_53, prime_sixtyTwoBH_223, prime_sixtyTwoBH_251, prime_sixtyTwoBH_281797123, prime_sixtyTwoBH_120443904577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419273 : Nat.totient 73300546814374981385704419273 = 48867026832641201588046833400 := by
  rw [← show ((([(3, 2), (11164651, 1), (729490353222614854147, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_11164651, prime_sixtyTwoBH_729490353222614854147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419274 : Nat.totient 73300546814374981385704419274 = 33266613215628967941200500560 := by
  rw [← show ((([(2, 1), (11, 1), (643, 1), (5181715454147814321059269, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_11, prime_sixtyTwoBH_643, prime_sixtyTwoBH_5181715454147814321059269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419275 : Nat.totient 73300546814374981385704419275 = 58223137574228668902971510400 := by
  rw [← show ((([(5, 2), (179, 1), (859, 1), (2971, 1), (26339, 1), (243679546004819, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_179, prime_sixtyTwoBH_859, prime_sixtyTwoBH_2971, prime_sixtyTwoBH_26339, prime_sixtyTwoBH_243679546004819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419276 : Nat.totient 73300546814374981385704419276 = 24433515604791660461901473088 := by
  rw [← show ((([(2, 2), (3, 1), (6108378901197915115475368273, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_6108378901197915115475368273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419277 : Nat.totient 73300546814374981385704419277 = 69203549143142502081316503840 := by
  rw [← show ((([(23, 1), (83, 2), (1063, 1), (617411, 1), (704880613782487, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_23, prime_sixtyTwoBH_83, prime_sixtyTwoBH_1063, prime_sixtyTwoBH_617411, prime_sixtyTwoBH_704880613782487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419278 : Nat.totient 73300546814374981385704419278 = 32678881551919496345329524096 := by
  rw [← show ((([(2, 1), (17, 1), (19, 1), (113468338721942695643505293, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_17, prime_sixtyTwoBH_19, prime_sixtyTwoBH_113468338721942695643505293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419279 : Nat.totient 73300546814374981385704419279 = 41832798826784812772204418912 := by
  rw [← show ((([(3, 1), (7, 1), (787, 1), (7568959, 1), (585972229872616703, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_7, prime_sixtyTwoBH_787, prime_sixtyTwoBH_7568959, prime_sixtyTwoBH_585972229872616703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419280 : Nat.totient 73300546814374981385704419280 = 29296055676488512350067200000 := by
  rw [← show ((([(2, 4), (5, 1), (1321, 1), (15991, 1), (223291, 1), (12834911, 1), (15134731, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_1321, prime_sixtyTwoBH_15991, prime_sixtyTwoBH_223291, prime_sixtyTwoBH_12834911, prime_sixtyTwoBH_15134731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419281 : Nat.totient 73300546814374981385704419281 = 73299890134456553363771460240 := by
  rw [← show ((([(111623, 1), (251038026307, 1), (2615857079821, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_111623, prime_sixtyTwoBH_251038026307, prime_sixtyTwoBH_2615857079821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419282 : Nat.totient 73300546814374981385704419282 = 24425241471501856310034912384 := by
  rw [← show ((([(2, 1), (3, 2), (2953, 1), (1379022214967358644423833, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_2953, prime_sixtyTwoBH_1379022214967358644423833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419283 : Nat.totient 73300546814374981385704419283 = 73300546814374981385704419282 := by
  rw [← show ((([(73300546814374981385704419283, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_73300546814374981385704419283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419284 : Nat.totient 73300546814374981385704419284 = 35752835589358384866060883200 := by
  rw [← show ((([(2, 2), (41, 1), (10133, 1), (6301611167, 1), (6999608045671, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_41, prime_sixtyTwoBH_10133, prime_sixtyTwoBH_6301611167, prime_sixtyTwoBH_6999608045671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419285 : Nat.totient 73300546814374981385704419285 = 32805839105808188625325209600 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (13, 1), (1175916793, 1), (29060516272098781, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_11, prime_sixtyTwoBH_13, prime_sixtyTwoBH_1175916793, prime_sixtyTwoBH_29060516272098781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419286 : Nat.totient 73300546814374981385704419286 = 31240811869678574441248610304 := by
  rw [← show ((([(2, 1), (7, 2), (193, 1), (2857, 1), (1356480607419989455907, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_7, prime_sixtyTwoBH_193, prime_sixtyTwoBH_2857, prime_sixtyTwoBH_1356480607419989455907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419287 : Nat.totient 73300546814374981385704419287 = 73106350462977858747558613440 := by
  rw [← show ((([(379, 1), (92399, 1), (35965406761, 1), (58199031427, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_379, prime_sixtyTwoBH_92399, prime_sixtyTwoBH_35965406761, prime_sixtyTwoBH_58199031427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419288 : Nat.totient 73300546814374981385704419288 = 23773150308549745078806254976 := by
  rw [← show ((([(2, 3), (3, 1), (37, 1), (2469700643, 1), (33423346696273607, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_37, prime_sixtyTwoBH_2469700643, prime_sixtyTwoBH_33423346696273607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419289 : Nat.totient 73300546814374981385704419289 = 73300546814373795991804326324 := by
  rw [← show ((([(65450207258983, 1), (1119943692833983, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_65450207258983, prime_sixtyTwoBH_1119943692833983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419290 : Nat.totient 73300546814374981385704419290 = 29089290144053957973254369280 := by
  rw [← show ((([(2, 1), (5, 1), (137, 1), (1721, 1), (3375149293, 1), (9211127402189, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_5, prime_sixtyTwoBH_137, prime_sixtyTwoBH_1721, prime_sixtyTwoBH_3375149293, prime_sixtyTwoBH_9211127402189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419291 : Nat.totient 73300546814374981385704419291 = 48574368148446495453085656768 := by
  rw [← show ((([(3, 3), (167, 1), (1053497, 1), (15430985952857658767, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_167, prime_sixtyTwoBH_1053497, prime_sixtyTwoBH_15430985952857658767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419292 : Nat.totient 73300546814374981385704419292 = 36650273407186744853887000896 := by
  rw [← show ((([(2, 2), (58232995172977, 1), (314686487431399, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_58232995172977, prime_sixtyTwoBH_314686487431399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419293 : Nat.totient 73300546814374981385704419293 = 62829040126607126902032359388 := by
  rw [← show ((([(7, 1), (10471506687767854483672059899, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_7, prime_sixtyTwoBH_10471506687767854483672059899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419294 : Nat.totient 73300546814374981385704419294 = 24191591133095828469682416000 := by
  rw [← show ((([(2, 1), (3, 1), (101, 1), (2854261, 1), (42378043929242305309, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_101, prime_sixtyTwoBH_2854261, prime_sixtyTwoBH_42378043929242305309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419295 : Nat.totient 73300546814374981385704419295 = 53893290937903215409111667712 := by
  rw [← show ((([(5, 1), (17, 1), (43, 2), (3797, 1), (122831789904267378959, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_5, prime_sixtyTwoBH_17, prime_sixtyTwoBH_43, prime_sixtyTwoBH_3797, prime_sixtyTwoBH_122831789904267378959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419296 : Nat.totient 73300546814374981385704419296 = 31947829042286025406211328000 := by
  rw [← show ((([(2, 5), (11, 1), (31, 1), (109, 1), (1649002021, 1), (37372759943747, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_11, prime_sixtyTwoBH_31, prime_sixtyTwoBH_109, prime_sixtyTwoBH_1649002021, prime_sixtyTwoBH_37372759943747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419297 : Nat.totient 73300546814374981385704419297 = 46295082198552619822550159520 := by
  rw [← show ((([(3, 1), (19, 1), (1285974505515350550626393321, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3, prime_sixtyTwoBH_19, prime_sixtyTwoBH_1285974505515350550626393321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419298 : Nat.totient 73300546814374981385704419298 = 33831001130045752464312801600 := by
  rw [← show ((([(2, 1), (13, 1), (1653101, 1), (2982708439, 1), (571773041407, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_13, prime_sixtyTwoBH_1653101, prime_sixtyTwoBH_2982708439, prime_sixtyTwoBH_571773041407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419299 : Nat.totient 73300546814374981385704419299 = 73277416315431483810300746496 := by
  rw [← show ((([(3169, 1), (53542646173, 1), (432001390069727, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_3169, prime_sixtyTwoBH_53542646173, prime_sixtyTwoBH_432001390069727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyTwoBH_73300546814374981385704419300 : Nat.totient 73300546814374981385704419300 = 15219677525692231983105792000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (7, 1), (23, 2), (29, 1), (61, 1), (12433206879297170711, 1)] : List FactorBlock).map factorBlockValue).prod) = 73300546814374981385704419300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyTwoBH_2, prime_sixtyTwoBH_3, prime_sixtyTwoBH_5, prime_sixtyTwoBH_7, prime_sixtyTwoBH_23, prime_sixtyTwoBH_29, prime_sixtyTwoBH_61, prime_sixtyTwoBH_12433206879297170711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyTwoBH : certifiedKill 1 73300546814374981385704419199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyTwoBH_73300546814374981385704419200, phi_sixtyTwoBH_73300546814374981385704419201, phi_sixtyTwoBH_73300546814374981385704419202,
    phi_sixtyTwoBH_73300546814374981385704419203, phi_sixtyTwoBH_73300546814374981385704419204, phi_sixtyTwoBH_73300546814374981385704419205,
    phi_sixtyTwoBH_73300546814374981385704419206, phi_sixtyTwoBH_73300546814374981385704419207, phi_sixtyTwoBH_73300546814374981385704419208,
    phi_sixtyTwoBH_73300546814374981385704419209, phi_sixtyTwoBH_73300546814374981385704419210, phi_sixtyTwoBH_73300546814374981385704419211,
    phi_sixtyTwoBH_73300546814374981385704419212, phi_sixtyTwoBH_73300546814374981385704419213, phi_sixtyTwoBH_73300546814374981385704419214,
    phi_sixtyTwoBH_73300546814374981385704419215, phi_sixtyTwoBH_73300546814374981385704419216, phi_sixtyTwoBH_73300546814374981385704419217,
    phi_sixtyTwoBH_73300546814374981385704419218, phi_sixtyTwoBH_73300546814374981385704419219, phi_sixtyTwoBH_73300546814374981385704419220,
    phi_sixtyTwoBH_73300546814374981385704419221, phi_sixtyTwoBH_73300546814374981385704419222, phi_sixtyTwoBH_73300546814374981385704419223,
    phi_sixtyTwoBH_73300546814374981385704419224, phi_sixtyTwoBH_73300546814374981385704419225, phi_sixtyTwoBH_73300546814374981385704419226,
    phi_sixtyTwoBH_73300546814374981385704419227, phi_sixtyTwoBH_73300546814374981385704419228, phi_sixtyTwoBH_73300546814374981385704419229,
    phi_sixtyTwoBH_73300546814374981385704419230, phi_sixtyTwoBH_73300546814374981385704419231, phi_sixtyTwoBH_73300546814374981385704419232,
    phi_sixtyTwoBH_73300546814374981385704419233, phi_sixtyTwoBH_73300546814374981385704419234, phi_sixtyTwoBH_73300546814374981385704419235,
    phi_sixtyTwoBH_73300546814374981385704419236, phi_sixtyTwoBH_73300546814374981385704419237, phi_sixtyTwoBH_73300546814374981385704419238,
    phi_sixtyTwoBH_73300546814374981385704419239, phi_sixtyTwoBH_73300546814374981385704419240, phi_sixtyTwoBH_73300546814374981385704419241,
    phi_sixtyTwoBH_73300546814374981385704419242, phi_sixtyTwoBH_73300546814374981385704419243, phi_sixtyTwoBH_73300546814374981385704419244,
    phi_sixtyTwoBH_73300546814374981385704419245, phi_sixtyTwoBH_73300546814374981385704419246, phi_sixtyTwoBH_73300546814374981385704419247,
    phi_sixtyTwoBH_73300546814374981385704419248, phi_sixtyTwoBH_73300546814374981385704419249, phi_sixtyTwoBH_73300546814374981385704419250,
    phi_sixtyTwoBH_73300546814374981385704419251, phi_sixtyTwoBH_73300546814374981385704419252, phi_sixtyTwoBH_73300546814374981385704419253,
    phi_sixtyTwoBH_73300546814374981385704419254, phi_sixtyTwoBH_73300546814374981385704419255, phi_sixtyTwoBH_73300546814374981385704419256,
    phi_sixtyTwoBH_73300546814374981385704419257, phi_sixtyTwoBH_73300546814374981385704419258, phi_sixtyTwoBH_73300546814374981385704419259,
    phi_sixtyTwoBH_73300546814374981385704419260, phi_sixtyTwoBH_73300546814374981385704419261, phi_sixtyTwoBH_73300546814374981385704419262,
    phi_sixtyTwoBH_73300546814374981385704419263, phi_sixtyTwoBH_73300546814374981385704419264, phi_sixtyTwoBH_73300546814374981385704419265,
    phi_sixtyTwoBH_73300546814374981385704419266, phi_sixtyTwoBH_73300546814374981385704419267, phi_sixtyTwoBH_73300546814374981385704419268,
    phi_sixtyTwoBH_73300546814374981385704419269, phi_sixtyTwoBH_73300546814374981385704419270, phi_sixtyTwoBH_73300546814374981385704419271,
    phi_sixtyTwoBH_73300546814374981385704419272, phi_sixtyTwoBH_73300546814374981385704419273, phi_sixtyTwoBH_73300546814374981385704419274,
    phi_sixtyTwoBH_73300546814374981385704419275, phi_sixtyTwoBH_73300546814374981385704419276, phi_sixtyTwoBH_73300546814374981385704419277,
    phi_sixtyTwoBH_73300546814374981385704419278, phi_sixtyTwoBH_73300546814374981385704419279, phi_sixtyTwoBH_73300546814374981385704419280,
    phi_sixtyTwoBH_73300546814374981385704419281, phi_sixtyTwoBH_73300546814374981385704419282, phi_sixtyTwoBH_73300546814374981385704419283,
    phi_sixtyTwoBH_73300546814374981385704419284, phi_sixtyTwoBH_73300546814374981385704419285, phi_sixtyTwoBH_73300546814374981385704419286,
    phi_sixtyTwoBH_73300546814374981385704419287, phi_sixtyTwoBH_73300546814374981385704419288, phi_sixtyTwoBH_73300546814374981385704419289,
    phi_sixtyTwoBH_73300546814374981385704419290, phi_sixtyTwoBH_73300546814374981385704419291, phi_sixtyTwoBH_73300546814374981385704419292,
    phi_sixtyTwoBH_73300546814374981385704419293, phi_sixtyTwoBH_73300546814374981385704419294, phi_sixtyTwoBH_73300546814374981385704419295,
    phi_sixtyTwoBH_73300546814374981385704419296, phi_sixtyTwoBH_73300546814374981385704419297, phi_sixtyTwoBH_73300546814374981385704419298,
    phi_sixtyTwoBH_73300546814374981385704419299, phi_sixtyTwoBH_73300546814374981385704419300]

end TotientTailPeriodKiller
end Erdos249257
