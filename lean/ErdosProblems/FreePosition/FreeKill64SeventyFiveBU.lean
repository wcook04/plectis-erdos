import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 75P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventyFiveBUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventyFiveBUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    seventyFiveBUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventyFiveBUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventyFiveBUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventyFiveBUFastPow a n * seventyFiveBUFastPow a n * a
        else seventyFiveBUFastPow a n * seventyFiveBUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventyFiveBU_2 : Nat.Prime 2 := by norm_num

private theorem prime_seventyFiveBU_3 : Nat.Prime 3 := by norm_num

private theorem prime_seventyFiveBU_5 : Nat.Prime 5 := by norm_num

private theorem prime_seventyFiveBU_7 : Nat.Prime 7 := by norm_num

private theorem prime_seventyFiveBU_11 : Nat.Prime 11 := by norm_num

private theorem prime_seventyFiveBU_13 : Nat.Prime 13 := by norm_num

private theorem prime_seventyFiveBU_17 : Nat.Prime 17 := by norm_num

private theorem prime_seventyFiveBU_19 : Nat.Prime 19 := by norm_num

private theorem prime_seventyFiveBU_23 : Nat.Prime 23 := by norm_num

private theorem prime_seventyFiveBU_29 : Nat.Prime 29 := by norm_num

private theorem prime_seventyFiveBU_31 : Nat.Prime 31 := by norm_num

private theorem prime_seventyFiveBU_37 : Nat.Prime 37 := by norm_num

private theorem prime_seventyFiveBU_41 : Nat.Prime 41 := by norm_num

private theorem prime_seventyFiveBU_43 : Nat.Prime 43 := by norm_num

private theorem prime_seventyFiveBU_47 : Nat.Prime 47 := by norm_num

private theorem prime_seventyFiveBU_53 : Nat.Prime 53 := by norm_num

private theorem prime_seventyFiveBU_59 : Nat.Prime 59 := by norm_num

private theorem prime_seventyFiveBU_61 : Nat.Prime 61 := by norm_num

private theorem prime_seventyFiveBU_67 : Nat.Prime 67 := by norm_num

private theorem prime_seventyFiveBU_71 : Nat.Prime 71 := by norm_num

private theorem prime_seventyFiveBU_73 : Nat.Prime 73 := by norm_num

private theorem prime_seventyFiveBU_79 : Nat.Prime 79 := by norm_num

private theorem prime_seventyFiveBU_83 : Nat.Prime 83 := by norm_num

private theorem prime_seventyFiveBU_89 : Nat.Prime 89 := by norm_num

private theorem prime_seventyFiveBU_97 : Nat.Prime 97 := by norm_num

private theorem prime_seventyFiveBU_101 : Nat.Prime 101 := by norm_num

private theorem prime_seventyFiveBU_103 : Nat.Prime 103 := by norm_num

private theorem prime_seventyFiveBU_107 : Nat.Prime 107 := by norm_num

private theorem prime_seventyFiveBU_109 : Nat.Prime 109 := by norm_num

private theorem prime_seventyFiveBU_113 : Nat.Prime 113 := by norm_num

private theorem prime_seventyFiveBU_127 : Nat.Prime 127 := by norm_num

private theorem prime_seventyFiveBU_131 : Nat.Prime 131 := by norm_num

private theorem prime_seventyFiveBU_137 : Nat.Prime 137 := by norm_num

private theorem prime_seventyFiveBU_139 : Nat.Prime 139 := by norm_num

private theorem prime_seventyFiveBU_149 : Nat.Prime 149 := by norm_num

private theorem prime_seventyFiveBU_151 : Nat.Prime 151 := by norm_num

private theorem prime_seventyFiveBU_157 : Nat.Prime 157 := by norm_num

private theorem prime_seventyFiveBU_163 : Nat.Prime 163 := by norm_num

private theorem prime_seventyFiveBU_167 : Nat.Prime 167 := by norm_num

private theorem prime_seventyFiveBU_173 : Nat.Prime 173 := by norm_num

private theorem prime_seventyFiveBU_179 : Nat.Prime 179 := by norm_num

private theorem prime_seventyFiveBU_181 : Nat.Prime 181 := by norm_num

private theorem prime_seventyFiveBU_191 : Nat.Prime 191 := by norm_num

private theorem prime_seventyFiveBU_193 : Nat.Prime 193 := by norm_num

private theorem prime_seventyFiveBU_197 : Nat.Prime 197 := by norm_num

private theorem prime_seventyFiveBU_199 : Nat.Prime 199 := by norm_num

private theorem prime_seventyFiveBU_211 : Nat.Prime 211 := by norm_num

private theorem prime_seventyFiveBU_223 : Nat.Prime 223 := by norm_num

private theorem prime_seventyFiveBU_227 : Nat.Prime 227 := by norm_num

private theorem prime_seventyFiveBU_229 : Nat.Prime 229 := by norm_num

private theorem prime_seventyFiveBU_233 : Nat.Prime 233 := by norm_num

private theorem prime_seventyFiveBU_239 : Nat.Prime 239 := by norm_num

private theorem prime_seventyFiveBU_241 : Nat.Prime 241 := by norm_num

private theorem prime_seventyFiveBU_269 : Nat.Prime 269 := by norm_num

private theorem prime_seventyFiveBU_271 : Nat.Prime 271 := by norm_num

private theorem prime_seventyFiveBU_277 : Nat.Prime 277 := by norm_num

private theorem prime_seventyFiveBU_281 : Nat.Prime 281 := by norm_num

private theorem prime_seventyFiveBU_283 : Nat.Prime 283 := by norm_num

private theorem prime_seventyFiveBU_293 : Nat.Prime 293 := by norm_num

private theorem prime_seventyFiveBU_307 : Nat.Prime 307 := by norm_num

private theorem prime_seventyFiveBU_311 : Nat.Prime 311 := by norm_num

private theorem prime_seventyFiveBU_331 : Nat.Prime 331 := by norm_num

private theorem prime_seventyFiveBU_349 : Nat.Prime 349 := by norm_num

private theorem prime_seventyFiveBU_353 : Nat.Prime 353 := by norm_num

private theorem prime_seventyFiveBU_367 : Nat.Prime 367 := by norm_num

private theorem prime_seventyFiveBU_379 : Nat.Prime 379 := by norm_num

private theorem prime_seventyFiveBU_383 : Nat.Prime 383 := by norm_num

private theorem prime_seventyFiveBU_389 : Nat.Prime 389 := by norm_num

private theorem prime_seventyFiveBU_397 : Nat.Prime 397 := by norm_num

private theorem prime_seventyFiveBU_401 : Nat.Prime 401 := by norm_num

private theorem prime_seventyFiveBU_421 : Nat.Prime 421 := by norm_num

private theorem prime_seventyFiveBU_433 : Nat.Prime 433 := by norm_num

private theorem prime_seventyFiveBU_457 : Nat.Prime 457 := by norm_num

private theorem prime_seventyFiveBU_463 : Nat.Prime 463 := by norm_num

private theorem prime_seventyFiveBU_487 : Nat.Prime 487 := by norm_num

private theorem prime_seventyFiveBU_509 : Nat.Prime 509 := by norm_num

private theorem prime_seventyFiveBU_523 : Nat.Prime 523 := by norm_num

private theorem prime_seventyFiveBU_563 : Nat.Prime 563 := by norm_num

private theorem prime_seventyFiveBU_571 : Nat.Prime 571 := by norm_num

private theorem prime_seventyFiveBU_587 : Nat.Prime 587 := by norm_num

private theorem prime_seventyFiveBU_613 : Nat.Prime 613 := by norm_num

private theorem prime_seventyFiveBU_619 : Nat.Prime 619 := by norm_num

private theorem prime_seventyFiveBU_641 : Nat.Prime 641 := by norm_num

private theorem prime_seventyFiveBU_643 : Nat.Prime 643 := by norm_num

private theorem prime_seventyFiveBU_659 : Nat.Prime 659 := by norm_num

private theorem prime_seventyFiveBU_709 : Nat.Prime 709 := by norm_num

private theorem prime_seventyFiveBU_719 : Nat.Prime 719 := by norm_num

private theorem prime_seventyFiveBU_739 : Nat.Prime 739 := by norm_num

private theorem prime_seventyFiveBU_743 : Nat.Prime 743 := by norm_num

private theorem prime_seventyFiveBU_773 : Nat.Prime 773 := by norm_num

private theorem prime_seventyFiveBU_787 : Nat.Prime 787 := by norm_num

private theorem prime_seventyFiveBU_811 : Nat.Prime 811 := by norm_num

private theorem prime_seventyFiveBU_827 : Nat.Prime 827 := by norm_num

private theorem prime_seventyFiveBU_829 : Nat.Prime 829 := by norm_num

private theorem prime_seventyFiveBU_859 : Nat.Prime 859 := by norm_num

private theorem prime_seventyFiveBU_929 : Nat.Prime 929 := by norm_num

private theorem prime_seventyFiveBU_937 : Nat.Prime 937 := by norm_num

private theorem prime_seventyFiveBU_947 : Nat.Prime 947 := by norm_num

private theorem prime_seventyFiveBU_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_seventyFiveBU_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_seventyFiveBU_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_seventyFiveBU_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_seventyFiveBU_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_seventyFiveBU_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_seventyFiveBU_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_seventyFiveBU_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_seventyFiveBU_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_seventyFiveBU_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_seventyFiveBU_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_seventyFiveBU_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_seventyFiveBU_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_seventyFiveBU_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_seventyFiveBU_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_seventyFiveBU_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_seventyFiveBU_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_seventyFiveBU_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_seventyFiveBU_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_seventyFiveBU_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_seventyFiveBU_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_seventyFiveBU_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_seventyFiveBU_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_seventyFiveBU_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_seventyFiveBU_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_seventyFiveBU_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_seventyFiveBU_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_seventyFiveBU_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_seventyFiveBU_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_seventyFiveBU_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_seventyFiveBU_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_seventyFiveBU_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_seventyFiveBU_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_seventyFiveBU_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_seventyFiveBU_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_seventyFiveBU_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_seventyFiveBU_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_seventyFiveBU_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_seventyFiveBU_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_seventyFiveBU_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_seventyFiveBU_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_seventyFiveBU_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_seventyFiveBU_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_seventyFiveBU_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_seventyFiveBU_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_seventyFiveBU_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_seventyFiveBU_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_seventyFiveBU_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_seventyFiveBU_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_seventyFiveBU_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_seventyFiveBU_3329 : Nat.Prime 3329 := by norm_num

private theorem prime_seventyFiveBU_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_seventyFiveBU_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_seventyFiveBU_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_seventyFiveBU_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_seventyFiveBU_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_seventyFiveBU_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_seventyFiveBU_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_seventyFiveBU_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_seventyFiveBU_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_seventyFiveBU_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_seventyFiveBU_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_seventyFiveBU_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_seventyFiveBU_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_seventyFiveBU_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_seventyFiveBU_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_seventyFiveBU_4643 : Nat.Prime 4643 := by norm_num

private theorem prime_seventyFiveBU_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_seventyFiveBU_4831 : Nat.Prime 4831 := by norm_num

private theorem prime_seventyFiveBU_4951 : Nat.Prime 4951 := by norm_num

private theorem prime_seventyFiveBU_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_seventyFiveBU_5009 : Nat.Prime 5009 := by norm_num

private theorem prime_seventyFiveBU_5011 : Nat.Prime 5011 := by norm_num

private theorem prime_seventyFiveBU_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_seventyFiveBU_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_seventyFiveBU_5443 : Nat.Prime 5443 := by norm_num

private theorem prime_seventyFiveBU_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_seventyFiveBU_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_seventyFiveBU_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_seventyFiveBU_6421 : Nat.Prime 6421 := by norm_num

private theorem prime_seventyFiveBU_6553 : Nat.Prime 6553 := by norm_num

private theorem prime_seventyFiveBU_6563 : Nat.Prime 6563 := by norm_num

private theorem prime_seventyFiveBU_7151 : Nat.Prime 7151 := by norm_num

private theorem prime_seventyFiveBU_7547 : Nat.Prime 7547 := by norm_num

private theorem prime_seventyFiveBU_7621 : Nat.Prime 7621 := by norm_num

private theorem prime_seventyFiveBU_8101 : Nat.Prime 8101 := by norm_num

private theorem prime_seventyFiveBU_8447 : Nat.Prime 8447 := by norm_num

private theorem prime_seventyFiveBU_8573 : Nat.Prime 8573 := by norm_num

private theorem prime_seventyFiveBU_8693 : Nat.Prime 8693 := by norm_num

private theorem prime_seventyFiveBU_9161 : Nat.Prime 9161 := by norm_num

private theorem prime_seventyFiveBU_9619 : Nat.Prime 9619 := by norm_num

private theorem prime_seventyFiveBU_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_seventyFiveBU_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_seventyFiveBU_10883 : Nat.Prime 10883 := by norm_num

private theorem prime_seventyFiveBU_11149 : Nat.Prime 11149 := by norm_num

private theorem prime_seventyFiveBU_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_seventyFiveBU_12277 : Nat.Prime 12277 := by norm_num

private theorem prime_seventyFiveBU_12457 : Nat.Prime 12457 := by norm_num

private theorem prime_seventyFiveBU_12589 : Nat.Prime 12589 := by norm_num

private theorem prime_seventyFiveBU_13037 : Nat.Prime 13037 := by norm_num

private theorem prime_seventyFiveBU_13567 : Nat.Prime 13567 := by norm_num

private theorem prime_seventyFiveBU_14207 : Nat.Prime 14207 := by norm_num

private theorem prime_seventyFiveBU_14369 : Nat.Prime 14369 := by norm_num

private theorem prime_seventyFiveBU_14489 : Nat.Prime 14489 := by norm_num

private theorem prime_seventyFiveBU_14627 : Nat.Prime 14627 := by norm_num

private theorem prime_seventyFiveBU_14629 : Nat.Prime 14629 := by norm_num

private theorem prime_seventyFiveBU_15907 : Nat.Prime 15907 := by norm_num

private theorem prime_seventyFiveBU_16633 : Nat.Prime 16633 := by norm_num

private theorem prime_seventyFiveBU_16987 : Nat.Prime 16987 := by norm_num

private theorem prime_seventyFiveBU_17257 : Nat.Prime 17257 := by norm_num

private theorem prime_seventyFiveBU_17321 : Nat.Prime 17321 := by norm_num

private theorem prime_seventyFiveBU_17881 : Nat.Prime 17881 := by norm_num

private theorem prime_seventyFiveBU_18287 : Nat.Prime 18287 := by norm_num

private theorem prime_seventyFiveBU_20117 : Nat.Prime 20117 := by norm_num

private theorem prime_seventyFiveBU_20393 : Nat.Prime 20393 := by norm_num

private theorem prime_seventyFiveBU_20521 : Nat.Prime 20521 := by norm_num

private theorem prime_seventyFiveBU_21499 : Nat.Prime 21499 := by norm_num

private theorem prime_seventyFiveBU_21517 : Nat.Prime 21517 := by norm_num

private theorem prime_seventyFiveBU_22877 : Nat.Prime 22877 := by norm_num

private theorem prime_seventyFiveBU_23027 : Nat.Prime 23027 := by norm_num

private theorem prime_seventyFiveBU_23173 : Nat.Prime 23173 := by norm_num

private theorem prime_seventyFiveBU_23857 : Nat.Prime 23857 := by norm_num

private theorem prime_seventyFiveBU_24509 : Nat.Prime 24509 := by norm_num

private theorem prime_seventyFiveBU_24919 : Nat.Prime 24919 := by norm_num

private theorem prime_seventyFiveBU_24971 : Nat.Prime 24971 := by norm_num

private theorem prime_seventyFiveBU_25703 : Nat.Prime 25703 := by norm_num

private theorem prime_seventyFiveBU_26557 : Nat.Prime 26557 := by norm_num

private theorem prime_seventyFiveBU_26633 : Nat.Prime 26633 := by norm_num

private theorem prime_seventyFiveBU_26849 : Nat.Prime 26849 := by norm_num

private theorem prime_seventyFiveBU_27059 : Nat.Prime 27059 := by norm_num

private theorem prime_seventyFiveBU_28201 : Nat.Prime 28201 := by norm_num

private theorem prime_seventyFiveBU_28753 : Nat.Prime 28753 := by norm_num

private theorem prime_seventyFiveBU_29641 : Nat.Prime 29641 := by norm_num

private theorem prime_seventyFiveBU_30427 : Nat.Prime 30427 := by norm_num

private theorem prime_seventyFiveBU_31151 : Nat.Prime 31151 := by norm_num

private theorem prime_seventyFiveBU_31667 : Nat.Prime 31667 := by norm_num

private theorem prime_seventyFiveBU_31721 : Nat.Prime 31721 := by norm_num

private theorem prime_seventyFiveBU_32257 : Nat.Prime 32257 := by norm_num

private theorem prime_seventyFiveBU_32831 : Nat.Prime 32831 := by norm_num

private theorem prime_seventyFiveBU_32917 : Nat.Prime 32917 := by norm_num

private theorem prime_seventyFiveBU_34949 : Nat.Prime 34949 := by norm_num

private theorem prime_seventyFiveBU_36083 : Nat.Prime 36083 := by norm_num

private theorem prime_seventyFiveBU_36473 : Nat.Prime 36473 := by norm_num

private theorem prime_seventyFiveBU_36887 : Nat.Prime 36887 := by norm_num

private theorem prime_seventyFiveBU_37489 : Nat.Prime 37489 := by norm_num

private theorem prime_seventyFiveBU_37813 : Nat.Prime 37813 := by norm_num

private theorem prime_seventyFiveBU_38119 : Nat.Prime 38119 := by norm_num

private theorem prime_seventyFiveBU_38917 : Nat.Prime 38917 := by norm_num

private theorem prime_seventyFiveBU_38933 : Nat.Prime 38933 := by norm_num

private theorem prime_seventyFiveBU_39191 : Nat.Prime 39191 := by norm_num

private theorem prime_seventyFiveBU_40433 : Nat.Prime 40433 := by norm_num

private theorem prime_seventyFiveBU_41627 : Nat.Prime 41627 := by norm_num

private theorem prime_seventyFiveBU_44267 : Nat.Prime 44267 := by norm_num

private theorem prime_seventyFiveBU_45707 : Nat.Prime 45707 := by norm_num

private theorem prime_seventyFiveBU_48341 : Nat.Prime 48341 := by norm_num

private theorem prime_seventyFiveBU_50033 : Nat.Prime 50033 := by norm_num

private theorem prime_seventyFiveBU_50273 : Nat.Prime 50273 := by norm_num

private theorem prime_seventyFiveBU_50821 : Nat.Prime 50821 := by norm_num

private theorem prime_seventyFiveBU_52301 : Nat.Prime 52301 := by norm_num

private theorem prime_seventyFiveBU_52529 : Nat.Prime 52529 := by norm_num

private theorem prime_seventyFiveBU_52859 : Nat.Prime 52859 := by norm_num

private theorem prime_seventyFiveBU_53831 : Nat.Prime 53831 := by norm_num

private theorem prime_seventyFiveBU_54037 : Nat.Prime 54037 := by norm_num

private theorem prime_seventyFiveBU_54727 : Nat.Prime 54727 := by norm_num

private theorem prime_seventyFiveBU_55849 : Nat.Prime 55849 := by norm_num

private theorem prime_seventyFiveBU_56249 : Nat.Prime 56249 := by norm_num

private theorem prime_seventyFiveBU_58099 : Nat.Prime 58099 := by norm_num

private theorem prime_seventyFiveBU_58169 : Nat.Prime 58169 := by norm_num

private theorem prime_seventyFiveBU_60383 : Nat.Prime 60383 := by norm_num

private theorem prime_seventyFiveBU_67213 : Nat.Prime 67213 := by norm_num

private theorem prime_seventyFiveBU_69259 : Nat.Prime 69259 := by norm_num

private theorem prime_seventyFiveBU_70079 : Nat.Prime 70079 := by norm_num

private theorem prime_seventyFiveBU_70489 : Nat.Prime 70489 := by norm_num

private theorem prime_seventyFiveBU_78901 : Nat.Prime 78901 := by norm_num

private theorem prime_seventyFiveBU_80681 : Nat.Prime 80681 := by norm_num

private theorem prime_seventyFiveBU_81749 : Nat.Prime 81749 := by norm_num

private theorem prime_seventyFiveBU_81929 : Nat.Prime 81929 := by norm_num

private theorem prime_seventyFiveBU_82219 : Nat.Prime 82219 := by norm_num

private theorem prime_seventyFiveBU_83477 : Nat.Prime 83477 := by norm_num

private theorem prime_seventyFiveBU_84047 : Nat.Prime 84047 := by norm_num

private theorem prime_seventyFiveBU_87557 : Nat.Prime 87557 := by norm_num

private theorem prime_seventyFiveBU_90977 : Nat.Prime 90977 := by norm_num

private theorem prime_seventyFiveBU_94151 : Nat.Prime 94151 := by norm_num

private theorem prime_seventyFiveBU_97127 : Nat.Prime 97127 := by norm_num

private theorem prime_seventyFiveBU_100853 : Nat.Prime 100853 := by norm_num

private theorem prime_seventyFiveBU_112429 : Nat.Prime 112429 := by norm_num

private theorem prime_seventyFiveBU_122849 : Nat.Prime 122849 := by norm_num

private theorem prime_seventyFiveBU_123817 : Nat.Prime 123817 := by norm_num

private theorem prime_seventyFiveBU_125299 : Nat.Prime 125299 := by norm_num

private theorem prime_seventyFiveBU_126547 : Nat.Prime 126547 := by norm_num

private theorem prime_seventyFiveBU_133493 : Nat.Prime 133493 := by norm_num

private theorem prime_seventyFiveBU_135353 : Nat.Prime 135353 := by norm_num

private theorem prime_seventyFiveBU_143797 : Nat.Prime 143797 := by norm_num

private theorem prime_seventyFiveBU_148723 : Nat.Prime 148723 := by norm_num

private theorem prime_seventyFiveBU_151091 : Nat.Prime 151091 := by norm_num

private theorem prime_seventyFiveBU_151141 : Nat.Prime 151141 := by norm_num

private theorem prime_seventyFiveBU_153877 : Nat.Prime 153877 := by norm_num

private theorem prime_seventyFiveBU_161947 : Nat.Prime 161947 := by norm_num

private theorem prime_seventyFiveBU_163433 : Nat.Prime 163433 := by norm_num

private theorem prime_seventyFiveBU_168719 : Nat.Prime 168719 := by norm_num

private theorem prime_seventyFiveBU_169241 : Nat.Prime 169241 := by norm_num

private theorem prime_seventyFiveBU_170167 : Nat.Prime 170167 := by norm_num

private theorem prime_seventyFiveBU_177109 : Nat.Prime 177109 := by norm_num

private theorem prime_seventyFiveBU_182059 : Nat.Prime 182059 := by norm_num

private theorem prime_seventyFiveBU_192233 : Nat.Prime 192233 := by norm_num

private theorem prime_seventyFiveBU_196873 : Nat.Prime 196873 := by norm_num

private theorem prime_seventyFiveBU_198943 : Nat.Prime 198943 := by norm_num

private theorem prime_seventyFiveBU_201953 : Nat.Prime 201953 := by norm_num

private theorem prime_seventyFiveBU_205211 : Nat.Prime 205211 := by norm_num

private theorem prime_seventyFiveBU_208963 : Nat.Prime 208963 := by norm_num

private theorem prime_seventyFiveBU_210853 : Nat.Prime 210853 := by norm_num

private theorem prime_seventyFiveBU_218047 : Nat.Prime 218047 := by norm_num

private theorem prime_seventyFiveBU_219361 : Nat.Prime 219361 := by norm_num

private theorem prime_seventyFiveBU_261509 : Nat.Prime 261509 := by norm_num

private theorem prime_seventyFiveBU_264977 : Nat.Prime 264977 := by norm_num

private theorem prime_seventyFiveBU_271079 : Nat.Prime 271079 := by norm_num

private theorem prime_seventyFiveBU_271177 : Nat.Prime 271177 := by norm_num

private theorem prime_seventyFiveBU_280843 : Nat.Prime 280843 := by norm_num

private theorem prime_seventyFiveBU_312553 : Nat.Prime 312553 := by norm_num

private theorem prime_seventyFiveBU_327247 : Nat.Prime 327247 := by norm_num

private theorem prime_seventyFiveBU_344327 : Nat.Prime 344327 := by norm_num

private theorem prime_seventyFiveBU_365983 : Nat.Prime 365983 := by norm_num

private theorem prime_seventyFiveBU_392279 : Nat.Prime 392279 := by norm_num

private theorem prime_seventyFiveBU_399379 : Nat.Prime 399379 := by norm_num

private theorem prime_seventyFiveBU_408491 : Nat.Prime 408491 := by norm_num

private theorem prime_seventyFiveBU_411083 : Nat.Prime 411083 := by norm_num

private theorem prime_seventyFiveBU_436097 : Nat.Prime 436097 := by norm_num

private theorem prime_seventyFiveBU_446003 : Nat.Prime 446003 := by norm_num

private theorem prime_seventyFiveBU_460813 : Nat.Prime 460813 := by norm_num

private theorem prime_seventyFiveBU_462541 : Nat.Prime 462541 := by norm_num

private theorem prime_seventyFiveBU_467627 : Nat.Prime 467627 := by norm_num

private theorem prime_seventyFiveBU_470059 : Nat.Prime 470059 := by norm_num

private theorem prime_seventyFiveBU_471503 : Nat.Prime 471503 := by norm_num

private theorem prime_seventyFiveBU_493043 : Nat.Prime 493043 := by norm_num

private theorem prime_seventyFiveBU_503963 : Nat.Prime 503963 := by norm_num

private theorem prime_seventyFiveBU_527063 : Nat.Prime 527063 := by norm_num

private theorem prime_seventyFiveBU_549019 : Nat.Prime 549019 := by norm_num

private theorem prime_seventyFiveBU_552991 : Nat.Prime 552991 := by norm_num

private theorem prime_seventyFiveBU_558491 : Nat.Prime 558491 := by norm_num

private theorem prime_seventyFiveBU_574711 : Nat.Prime 574711 := by norm_num

private theorem prime_seventyFiveBU_575753 : Nat.Prime 575753 := by norm_num

private theorem prime_seventyFiveBU_577547 : Nat.Prime 577547 := by norm_num

private theorem prime_seventyFiveBU_584387 : Nat.Prime 584387 := by norm_num

private theorem prime_seventyFiveBU_615721 : Nat.Prime 615721 := by norm_num

private theorem prime_seventyFiveBU_617237 : Nat.Prime 617237 := by norm_num

private theorem prime_seventyFiveBU_620827 : Nat.Prime 620827 := by norm_num

private theorem prime_seventyFiveBU_621617 : Nat.Prime 621617 := by norm_num

private theorem prime_seventyFiveBU_652429 : Nat.Prime 652429 := by norm_num

private theorem prime_seventyFiveBU_666821 : Nat.Prime 666821 := by norm_num

private theorem prime_seventyFiveBU_674123 : Nat.Prime 674123 := by norm_num

private theorem prime_seventyFiveBU_687431 : Nat.Prime 687431 := by norm_num

private theorem prime_seventyFiveBU_705833 : Nat.Prime 705833 := by norm_num

private theorem prime_seventyFiveBU_768161 : Nat.Prime 768161 := by norm_num

private theorem prime_seventyFiveBU_769997 : Nat.Prime 769997 := by norm_num

private theorem prime_seventyFiveBU_792643 : Nat.Prime 792643 := by norm_num

private theorem prime_seventyFiveBU_815317 : Nat.Prime 815317 := by norm_num

private theorem prime_seventyFiveBU_849581 : Nat.Prime 849581 := by norm_num

private theorem prime_seventyFiveBU_856139 : Nat.Prime 856139 := by norm_num

private theorem prime_seventyFiveBU_896293 : Nat.Prime 896293 := by norm_num

private theorem prime_seventyFiveBU_906949 : Nat.Prime 906949 := by norm_num

private theorem prime_seventyFiveBU_943843 : Nat.Prime 943843 := by norm_num

private theorem prime_seventyFiveBU_960737 : Nat.Prime 960737 := by norm_num

private theorem prime_seventyFiveBU_977269 : Nat.Prime 977269 := by norm_num

private theorem prime_seventyFiveBU_1060883 : Nat.Prime 1060883 := by norm_num

private theorem prime_seventyFiveBU_1065949 : Nat.Prime 1065949 := by norm_num

private theorem prime_seventyFiveBU_1194547 : Nat.Prime 1194547 := by norm_num

private theorem prime_seventyFiveBU_1263547 : Nat.Prime 1263547 := by norm_num

private theorem prime_seventyFiveBU_1265981 : Nat.Prime 1265981 := by norm_num

private theorem prime_seventyFiveBU_1301123 : Nat.Prime 1301123 := by norm_num

private theorem prime_seventyFiveBU_1326041 : Nat.Prime 1326041 := by norm_num

private theorem prime_seventyFiveBU_1420369 : Nat.Prime 1420369 := by norm_num

private theorem prime_seventyFiveBU_1425649 : Nat.Prime 1425649 := by norm_num

private theorem prime_seventyFiveBU_1600217 : Nat.Prime 1600217 := by norm_num

private theorem prime_seventyFiveBU_1718069 : Nat.Prime 1718069 := by norm_num

private theorem prime_seventyFiveBU_1798543 : Nat.Prime 1798543 := by norm_num

private theorem prime_seventyFiveBU_1853779 : Nat.Prime 1853779 := by norm_num

private theorem prime_seventyFiveBU_1901033 : Nat.Prime 1901033 := by norm_num

private theorem prime_seventyFiveBU_2116571 : Nat.Prime 2116571 := by norm_num

private theorem prime_seventyFiveBU_2162197 : Nat.Prime 2162197 := by norm_num

private theorem prime_seventyFiveBU_2169031 : Nat.Prime 2169031 := by norm_num

private theorem prime_seventyFiveBU_2255161 : Nat.Prime 2255161 := by norm_num

private theorem prime_seventyFiveBU_2289863 : Nat.Prime 2289863 := by norm_num

private theorem prime_seventyFiveBU_2359789 : Nat.Prime 2359789 := by norm_num

private theorem prime_seventyFiveBU_2363393 : Nat.Prime 2363393 := by norm_num

private theorem prime_seventyFiveBU_2429617 : Nat.Prime 2429617 := by norm_num

private theorem prime_seventyFiveBU_2449999 : Nat.Prime 2449999 := by norm_num

private theorem prime_seventyFiveBU_2534153 : Nat.Prime 2534153 := by norm_num

private theorem prime_seventyFiveBU_2536393 : Nat.Prime 2536393 := by norm_num

private theorem prime_seventyFiveBU_2627297 : Nat.Prime 2627297 := by norm_num

private theorem prime_seventyFiveBU_2658793 : Nat.Prime 2658793 := by norm_num

private theorem prime_seventyFiveBU_2810641 : Nat.Prime 2810641 := by norm_num

private theorem prime_seventyFiveBU_2954093 : Nat.Prime 2954093 := by norm_num

private theorem prime_seventyFiveBU_2976781 : Nat.Prime 2976781 := by norm_num

private theorem prime_seventyFiveBU_3146359 : Nat.Prime 3146359 := by norm_num

private theorem prime_seventyFiveBU_3341413 : Nat.Prime 3341413 := by norm_num

private theorem prime_seventyFiveBU_3390953 : Nat.Prime 3390953 := by norm_num

private theorem prime_seventyFiveBU_3535627 : Nat.Prime 3535627 := by norm_num

private theorem prime_seventyFiveBU_3553273 : Nat.Prime 3553273 := by norm_num

private theorem prime_seventyFiveBU_3670243 : Nat.Prime 3670243 := by norm_num

private theorem prime_seventyFiveBU_4109431 : Nat.Prime 4109431 := by norm_num

private theorem prime_seventyFiveBU_4318543 : Nat.Prime 4318543 := by norm_num

private theorem prime_seventyFiveBU_4854739 : Nat.Prime 4854739 := by norm_num

private theorem prime_seventyFiveBU_5024783 : Nat.Prime 5024783 := by norm_num

private theorem prime_seventyFiveBU_5122297 : Nat.Prime 5122297 := by norm_num

private theorem prime_seventyFiveBU_5265961 : Nat.Prime 5265961 := by norm_num

private theorem prime_seventyFiveBU_5397163 : Nat.Prime 5397163 := by norm_num

private theorem prime_seventyFiveBU_5882053 : Nat.Prime 5882053 := by norm_num

private theorem prime_seventyFiveBU_5920939 : Nat.Prime 5920939 := by norm_num

private theorem prime_seventyFiveBU_6091663 : Nat.Prime 6091663 := by norm_num

private theorem prime_seventyFiveBU_6095413 : Nat.Prime 6095413 := by norm_num

private theorem prime_seventyFiveBU_6133997 : Nat.Prime 6133997 := by norm_num

private theorem prime_seventyFiveBU_6811213 : Nat.Prime 6811213 := by norm_num

private theorem prime_seventyFiveBU_7818821 : Nat.Prime 7818821 := by norm_num

private theorem prime_seventyFiveBU_9435199 : Nat.Prime 9435199 := by norm_num

private theorem prime_seventyFiveBU_9590299 : Nat.Prime 9590299 := by norm_num

private theorem prime_seventyFiveBU_10315681 : Nat.Prime 10315681 := by norm_num

private theorem prime_seventyFiveBU_10729309 : Nat.Prime 10729309 := by norm_num

private theorem prime_seventyFiveBU_10830103 : Nat.Prime 10830103 := by norm_num

private theorem prime_seventyFiveBU_12115933 : Nat.Prime 12115933 := by norm_num

private theorem prime_seventyFiveBU_12212917 : Nat.Prime 12212917 := by norm_num

private theorem prime_seventyFiveBU_12410441 : Nat.Prime 12410441 := by norm_num

private theorem prime_seventyFiveBU_13683277 : Nat.Prime 13683277 := by norm_num

private theorem prime_seventyFiveBU_14212073 : Nat.Prime 14212073 := by norm_num

private theorem prime_seventyFiveBU_15063991 : Nat.Prime 15063991 := by norm_num

private theorem prime_seventyFiveBU_15118249 : Nat.Prime 15118249 := by norm_num

private theorem prime_seventyFiveBU_15518747 : Nat.Prime 15518747 := by norm_num

private theorem prime_seventyFiveBU_17975863 : Nat.Prime 17975863 := by norm_num

private theorem prime_seventyFiveBU_18112217 : Nat.Prime 18112217 := by norm_num

private theorem prime_seventyFiveBU_18126803 : Nat.Prime 18126803 := by norm_num

private theorem prime_seventyFiveBU_18160367 : Nat.Prime 18160367 := by norm_num

private theorem prime_seventyFiveBU_23628991 : Nat.Prime 23628991 := by norm_num

private theorem prime_seventyFiveBU_24644377 : Nat.Prime 24644377 := by norm_num

private theorem prime_seventyFiveBU_26879933 : Nat.Prime 26879933 := by norm_num

private theorem prime_seventyFiveBU_27052391 : Nat.Prime 27052391 := by norm_num

private theorem prime_seventyFiveBU_30925243 : Nat.Prime 30925243 := by
  apply lucas_primality 30925243 (3 : ZMod 30925243)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1718069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1718069, 1)] : List FactorBlock).map factorBlockValue).prod) = 30925243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1718069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30925243) ^ 15462621 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 30925243) ^ 10308414 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 30925243) ^ 18 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_31772929 : Nat.Prime 31772929 := by
  apply lucas_primality 31772929 (14 : ZMod 31772929)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (11, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (11, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) = 31772929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_3761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 31772929) ^ 15886464 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31772929) ^ 10590976 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31772929) ^ 2888448 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31772929) ^ 8448 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_32242169 : Nat.Prime 32242169 := by
  apply lucas_primality 32242169 (3 : ZMod 32242169)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (575753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (575753, 1)] : List FactorBlock).map factorBlockValue).prod) = 32242169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_575753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32242169) ^ 16121084 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 32242169) ^ 4606024 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 32242169) ^ 56 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_32836511 : Nat.Prime 32836511 := by
  apply lucas_primality 32836511 (7 : ZMod 32836511)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (293, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (293, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) = 32836511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_293
      · exact prime_seventyFiveBU_1601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32836511) ^ 16418255 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32836511) ^ 6567302 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32836511) ^ 4690930 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32836511) ^ 112070 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 32836511) ^ 20510 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_33917087 : Nat.Prime 33917087 := by
  apply lucas_primality 33917087 (5 : ZMod 33917087)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (41, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (41, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 33917087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33917087) ^ 16958543 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33917087) ^ 4845298 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33917087) ^ 916678 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33917087) ^ 827246 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 33917087) ^ 21238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_35292319 : Nat.Prime 35292319 := by
  apply lucas_primality 35292319 (6 : ZMod 35292319)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5882053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5882053, 1)] : List FactorBlock).map factorBlockValue).prod) = 35292319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5882053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 35292319) ^ 17646159 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 35292319) ^ 11764106 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 35292319) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_35782429 : Nat.Prime 35782429 := by
  apply lucas_primality 35782429 (10 : ZMod 35782429)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (271079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (271079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35782429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_271079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 35782429) ^ 17891214 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35782429) ^ 11927476 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35782429) ^ 3252948 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35782429) ^ 132 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_36242267 : Nat.Prime 36242267 := by
  apply lucas_primality 36242267 (2 : ZMod 36242267)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1065949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1065949, 1)] : List FactorBlock).map factorBlockValue).prod) = 36242267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_1065949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36242267) ^ 18121133 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36242267) ^ 2131898 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36242267) ^ 34 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_38098279 : Nat.Prime 38098279 := by
  apply lucas_primality 38098279 (6 : ZMod 38098279)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2116571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2116571, 1)] : List FactorBlock).map factorBlockValue).prod) = 38098279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_2116571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 38098279) ^ 19049139 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 38098279) ^ 12699426 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 38098279) ^ 18 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_38383237 : Nat.Prime 38383237 := by
  apply lucas_primality 38383237 (2 : ZMod 38383237)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (53, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (53, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) = 38383237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_53
      · exact prime_seventyFiveBU_20117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38383237) ^ 19191618 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38383237) ^ 12794412 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38383237) ^ 724212 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38383237) ^ 1908 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_39567947 : Nat.Prime 39567947 := by
  apply lucas_primality 39567947 (2 : ZMod 39567947)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1798543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1798543, 1)] : List FactorBlock).map factorBlockValue).prod) = 39567947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_1798543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39567947) ^ 19783973 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39567947) ^ 3597086 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39567947) ^ 22 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_40009261 : Nat.Prime 40009261 := by
  apply lucas_primality 40009261 (6 : ZMod 40009261)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (666821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (666821, 1)] : List FactorBlock).map factorBlockValue).prod) = 40009261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_666821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40009261) ^ 20004630 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 40009261) ^ 13336420 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 40009261) ^ 8001852 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 40009261) ^ 60 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_40096957 : Nat.Prime 40096957 := by
  apply lucas_primality 40096957 (2 : ZMod 40096957)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3341413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3341413, 1)] : List FactorBlock).map factorBlockValue).prod) = 40096957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_3341413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40096957) ^ 20048478 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 40096957) ^ 13365652 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 40096957) ^ 12 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_41863307 : Nat.Prime 41863307 := by
  apply lucas_primality 41863307 (2 : ZMod 41863307)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (433, 1), (48341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (433, 1), (48341, 1)] : List FactorBlock).map factorBlockValue).prod) = 41863307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_433
      · exact prime_seventyFiveBU_48341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41863307) ^ 20931653 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41863307) ^ 96682 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 41863307) ^ 866 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_43185431 : Nat.Prime 43185431 := by
  apply lucas_primality 43185431 (7 : ZMod 43185431)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4318543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4318543, 1)] : List FactorBlock).map factorBlockValue).prod) = 43185431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_4318543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 43185431) ^ 21592715 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43185431) ^ 8637086 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43185431) ^ 10 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_43308823 : Nat.Prime 43308823 := by
  apply lucas_primality 43308823 (5 : ZMod 43308823)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (70079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (70079, 1)] : List FactorBlock).map factorBlockValue).prod) = 43308823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_103
      · exact prime_seventyFiveBU_70079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43308823) ^ 21654411 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43308823) ^ 14436274 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43308823) ^ 420474 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43308823) ^ 618 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_43418773 : Nat.Prime 43418773 := by
  apply lucas_primality 43418773 (2 : ZMod 43418773)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (16987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (16987, 1)] : List FactorBlock).map factorBlockValue).prod) = 43418773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_71
      · exact prime_seventyFiveBU_16987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43418773) ^ 21709386 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 43418773) ^ 14472924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 43418773) ^ 611532 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 43418773) ^ 2556 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_44103361 : Nat.Prime 44103361 := by
  apply lucas_primality 44103361 (19 : ZMod 44103361)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) = 44103361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_6563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 44103361) ^ 22051680 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (19 : ZMod 44103361) ^ 14701120 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (19 : ZMod 44103361) ^ 8820672 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (19 : ZMod 44103361) ^ 6300480 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (19 : ZMod 44103361) ^ 6720 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_45624793 : Nat.Prime 45624793 := by
  apply lucas_primality 45624793 (10 : ZMod 45624793)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1901033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1901033, 1)] : List FactorBlock).map factorBlockValue).prod) = 45624793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1901033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 45624793) ^ 22812396 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 45624793) ^ 15208264 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 45624793) ^ 24 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_48636503 : Nat.Prime 48636503 := by
  apply lucas_primality 48636503 (5 : ZMod 48636503)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1063, 1), (22877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1063, 1), (22877, 1)] : List FactorBlock).map factorBlockValue).prod) = 48636503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_1063
      · exact prime_seventyFiveBU_22877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48636503) ^ 24318251 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48636503) ^ 45754 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 48636503) ^ 2126 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_51457891 : Nat.Prime 51457891 := by
  apply lucas_primality 51457891 (2 : ZMod 51457891)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (29, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (29, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 51457891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51457891) ^ 25728945 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 17152630 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 10291578 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 4677990 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 2708310 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 1774410 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 51457891) ^ 181830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_57327013 : Nat.Prime 57327013 := by
  apply lucas_primality 57327013 (5 : ZMod 57327013)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (211, 1), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (211, 1), (7547, 1)] : List FactorBlock).map factorBlockValue).prod) = 57327013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_211
      · exact prime_seventyFiveBU_7547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57327013) ^ 28663506 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 57327013) ^ 19109004 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 57327013) ^ 271692 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 57327013) ^ 7596 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_59239073 : Nat.Prime 59239073 := by
  apply lucas_primality 59239073 (3 : ZMod 59239073)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (50033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (50033, 1)] : List FactorBlock).map factorBlockValue).prod) = 59239073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_50033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59239073) ^ 29619536 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 59239073) ^ 1601056 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 59239073) ^ 1184 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_59436569 : Nat.Prime 59436569 := by
  apply lucas_primality 59436569 (3 : ZMod 59436569)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (811, 1), (9161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (811, 1), (9161, 1)] : List FactorBlock).map factorBlockValue).prod) = 59436569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_811
      · exact prime_seventyFiveBU_9161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59436569) ^ 29718284 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 59436569) ^ 73288 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 59436569) ^ 6488 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_60693887 : Nat.Prime 60693887 := by
  apply lucas_primality 60693887 (5 : ZMod 60693887)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (421, 1), (6553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (421, 1), (6553, 1)] : List FactorBlock).map factorBlockValue).prod) = 60693887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_421
      · exact prime_seventyFiveBU_6553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60693887) ^ 30346943 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 60693887) ^ 5517626 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 60693887) ^ 144166 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 60693887) ^ 9262 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_61567109 : Nat.Prime 61567109 := by
  apply lucas_primality 61567109 (2 : ZMod 61567109)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (67213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (67213, 1)] : List FactorBlock).map factorBlockValue).prod) = 61567109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_229
      · exact prime_seventyFiveBU_67213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61567109) ^ 30783554 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 61567109) ^ 268852 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 61567109) ^ 916 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_61572101 : Nat.Prime 61572101 := by
  apply lucas_primality 61572101 (2 : ZMod 61572101)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (615721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (615721, 1)] : List FactorBlock).map factorBlockValue).prod) = 61572101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_615721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61572101) ^ 30786050 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 61572101) ^ 12314420 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 61572101) ^ 100 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_65548169 : Nat.Prime 65548169 := by
  apply lucas_primality 65548169 (3 : ZMod 65548169)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (43, 1), (163, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (43, 1), (163, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 65548169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_163
      · exact prime_seventyFiveBU_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65548169) ^ 32774084 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 65548169) ^ 9364024 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 65548169) ^ 1524376 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 65548169) ^ 402136 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 65548169) ^ 392504 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_67711169 : Nat.Prime 67711169 := by
  apply lucas_primality 67711169 (3 : ZMod 67711169)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (151141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (151141, 1)] : List FactorBlock).map factorBlockValue).prod) = 67711169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_151141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67711169) ^ 33855584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 67711169) ^ 9673024 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 67711169) ^ 448 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_72235213 : Nat.Prime 72235213 := by
  apply lucas_primality 72235213 (2 : ZMod 72235213)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (122849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (122849, 1)] : List FactorBlock).map factorBlockValue).prod) = 72235213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_122849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72235213) ^ 36117606 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 72235213) ^ 24078404 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 72235213) ^ 10319316 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 72235213) ^ 588 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_84455759 : Nat.Prime 84455759 := by
  apply lucas_primality 84455759 (11 : ZMod 84455759)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2447, 1), (17257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2447, 1), (17257, 1)] : List FactorBlock).map factorBlockValue).prod) = 84455759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_2447
      · exact prime_seventyFiveBU_17257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 84455759) ^ 42227879 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 84455759) ^ 34514 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 84455759) ^ 4894 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_85550791 : Nat.Prime 85550791 := by
  apply lucas_primality 85550791 (14 : ZMod 85550791)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (219361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (219361, 1)] : List FactorBlock).map factorBlockValue).prod) = 85550791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_219361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 85550791) ^ 42775395 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 85550791) ^ 28516930 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 85550791) ^ 17110158 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 85550791) ^ 6580830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (14 : ZMod 85550791) ^ 390 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_88085341 : Nat.Prime 88085341 := by
  apply lucas_primality 88085341 (2 : ZMod 88085341)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 2), (3329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 2), (3329, 1)] : List FactorBlock).map factorBlockValue).prod) = 88085341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_3329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88085341) ^ 44042670 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 88085341) ^ 29361780 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 88085341) ^ 17617068 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 88085341) ^ 12583620 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 88085341) ^ 26460 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_94377221 : Nat.Prime 94377221 := by
  apply lucas_primality 94377221 (3 : ZMod 94377221)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (674123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (674123, 1)] : List FactorBlock).map factorBlockValue).prod) = 94377221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_674123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94377221) ^ 47188610 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94377221) ^ 18875444 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94377221) ^ 13482460 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94377221) ^ 140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_96559493 : Nat.Prime 96559493 := by
  apply lucas_primality 96559493 (2 : ZMod 96559493)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (652429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (652429, 1)] : List FactorBlock).map factorBlockValue).prod) = 96559493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_652429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96559493) ^ 48279746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 96559493) ^ 2609716 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 96559493) ^ 148 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_99482087 : Nat.Prime 99482087 := by
  apply lucas_primality 99482087 (5 : ZMod 99482087)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (411083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (411083, 1)] : List FactorBlock).map factorBlockValue).prod) = 99482087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_411083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 99482087) ^ 49741043 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 99482087) ^ 9043826 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 99482087) ^ 242 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_101212019 : Nat.Prime 101212019 := by
  apply lucas_primality 101212019 (2 : ZMod 101212019)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (433, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (433, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) = 101212019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_73
      · exact prime_seventyFiveBU_433
      · exact prime_seventyFiveBU_1601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101212019) ^ 50606009 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 101212019) ^ 1386466 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 101212019) ^ 233746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 101212019) ^ 63218 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_104959219 : Nat.Prime 104959219 := by
  apply lucas_primality 104959219 (7 : ZMod 104959219)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (192233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (192233, 1)] : List FactorBlock).map factorBlockValue).prod) = 104959219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_192233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 104959219) ^ 52479609 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 104959219) ^ 34986406 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 104959219) ^ 14994174 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 104959219) ^ 8073786 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 104959219) ^ 546 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_108470801 : Nat.Prime 108470801 := by
  apply lucas_primality 108470801 (6 : ZMod 108470801)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (271177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (271177, 1)] : List FactorBlock).map factorBlockValue).prod) = 108470801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_271177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 108470801) ^ 54235400 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 108470801) ^ 21694160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 108470801) ^ 400 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_112287419 : Nat.Prime 112287419 := by
  apply lucas_primality 112287419 (2 : ZMod 112287419)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1194547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1194547, 1)] : List FactorBlock).map factorBlockValue).prod) = 112287419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_47
      · exact prime_seventyFiveBU_1194547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 112287419) ^ 56143709 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112287419) ^ 2389094 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 112287419) ^ 94 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_132045437 : Nat.Prime 132045437 := by
  apply lucas_primality 132045437 (2 : ZMod 132045437)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (223, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (223, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) = 132045437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_179
      · exact prime_seventyFiveBU_223
      · exact prime_seventyFiveBU_827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 132045437) ^ 66022718 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132045437) ^ 737684 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132045437) ^ 592132 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 132045437) ^ 159668 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_173284273 : Nat.Prime 173284273 := by
  apply lucas_primality 173284273 (5 : ZMod 173284273)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (7, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (7, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) = 173284273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_6367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 173284273) ^ 86642136 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 173284273) ^ 57761424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 173284273) ^ 24754896 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 173284273) ^ 27216 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_180781709 : Nat.Prime 180781709 := by
  apply lucas_primality 180781709 (2 : ZMod 180781709)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (31, 1), (50273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (31, 1), (50273, 1)] : List FactorBlock).map factorBlockValue).prod) = 180781709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_31
      · exact prime_seventyFiveBU_50273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 180781709) ^ 90390854 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180781709) ^ 6233852 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180781709) ^ 5831668 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 180781709) ^ 3596 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_194439989 : Nat.Prime 194439989 := by
  apply lucas_primality 194439989 (2 : ZMod 194439989)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2111, 1), (23027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2111, 1), (23027, 1)] : List FactorBlock).map factorBlockValue).prod) = 194439989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_2111
      · exact prime_seventyFiveBU_23027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 194439989) ^ 97219994 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 194439989) ^ 92108 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 194439989) ^ 8444 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_196538917 : Nat.Prime 196538917 := by
  apply lucas_primality 196538917 (2 : ZMod 196538917)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (80681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (80681, 1)] : List FactorBlock).map factorBlockValue).prod) = 196538917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_80681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 196538917) ^ 98269458 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196538917) ^ 65512972 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196538917) ^ 28076988 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196538917) ^ 6777204 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196538917) ^ 2436 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_235534753 : Nat.Prime 235534753 := by
  apply lucas_primality 235534753 (5 : ZMod 235534753)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (29, 1), (28201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (29, 1), (28201, 1)] : List FactorBlock).map factorBlockValue).prod) = 235534753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_28201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 235534753) ^ 117767376 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 235534753) ^ 78511584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 235534753) ^ 8121888 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 235534753) ^ 8352 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_252446429 : Nat.Prime 252446429 := by
  apply lucas_primality 252446429 (2 : ZMod 252446429)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (4854739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (4854739, 1)] : List FactorBlock).map factorBlockValue).prod) = 252446429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_4854739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 252446429) ^ 126223214 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252446429) ^ 19418956 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 252446429) ^ 52 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_255462721 : Nat.Prime 255462721 := by
  apply lucas_primality 255462721 (11 : ZMod 255462721)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (281, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (281, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 255462721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_281
      · exact prime_seventyFiveBU_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 255462721) ^ 127731360 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 255462721) ^ 85154240 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 255462721) ^ 51092544 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 255462721) ^ 909120 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 255462721) ^ 269760 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_284309737 : Nat.Prime 284309737 := by
  apply lucas_primality 284309737 (5 : ZMod 284309737)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (408491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (408491, 1)] : List FactorBlock).map factorBlockValue).prod) = 284309737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_408491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284309737) ^ 142154868 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284309737) ^ 94769912 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284309737) ^ 9803784 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284309737) ^ 696 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_300803227 : Nat.Prime 300803227 := by
  apply lucas_primality 300803227 (2 : ZMod 300803227)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (199, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (199, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 300803227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_191
      · exact prime_seventyFiveBU_199
      · exact prime_seventyFiveBU_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 300803227) ^ 150401613 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300803227) ^ 100267742 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300803227) ^ 1574886 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300803227) ^ 1511574 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300803227) ^ 228054 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_335374499 : Nat.Prime 335374499 := by
  apply lucas_primality 335374499 (2 : ZMod 335374499)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (487, 1), (344327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (487, 1), (344327, 1)] : List FactorBlock).map factorBlockValue).prod) = 335374499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_487
      · exact prime_seventyFiveBU_344327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 335374499) ^ 167687249 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 335374499) ^ 688654 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 335374499) ^ 974 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_353880169 : Nat.Prime 353880169 := by
  apply lucas_primality 353880169 (7 : ZMod 353880169)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (193, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (193, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 353880169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_193
      · exact prime_seventyFiveBU_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 353880169) ^ 176940084 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 353880169) ^ 117960056 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 353880169) ^ 18625272 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 353880169) ^ 1833576 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 353880169) ^ 88008 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_364593499 : Nat.Prime 364593499 := by
  apply lucas_primality 364593499 (3 : ZMod 364593499)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (906949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (906949, 1)] : List FactorBlock).map factorBlockValue).prod) = 364593499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_67
      · exact prime_seventyFiveBU_906949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 364593499) ^ 182296749 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 364593499) ^ 121531166 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 364593499) ^ 5441694 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 364593499) ^ 402 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_396708707 : Nat.Prime 396708707 := by
  apply lucas_primality 396708707 (2 : ZMod 396708707)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (1853779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (1853779, 1)] : List FactorBlock).map factorBlockValue).prod) = 396708707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_107
      · exact prime_seventyFiveBU_1853779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 396708707) ^ 198354353 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 396708707) ^ 3707558 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 396708707) ^ 214 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_454864327 : Nat.Prime 454864327 := by
  apply lucas_primality 454864327 (3 : ZMod 454864327)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10830103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10830103, 1)] : List FactorBlock).map factorBlockValue).prod) = 454864327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_10830103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454864327) ^ 227432163 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 454864327) ^ 151621442 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 454864327) ^ 64980618 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 454864327) ^ 42 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_492536873 : Nat.Prime 492536873 := by
  apply lucas_primality 492536873 (3 : ZMod 492536873)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61567109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61567109, 1)] : List FactorBlock).map factorBlockValue).prod) = 492536873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_61567109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 492536873) ^ 246268436 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 492536873) ^ 8 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_636227069 : Nat.Prime 636227069 := by
  apply lucas_primality 636227069 (2 : ZMod 636227069)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3821, 1), (41627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3821, 1), (41627, 1)] : List FactorBlock).map factorBlockValue).prod) = 636227069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3821
      · exact prime_seventyFiveBU_41627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 636227069) ^ 318113534 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 636227069) ^ 166508 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 636227069) ^ 15284 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_743111791 : Nat.Prime 743111791 := by
  apply lucas_primality 743111791 (6 : ZMod 743111791)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (181, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (181, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 743111791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_107
      · exact prime_seventyFiveBU_181
      · exact prime_seventyFiveBU_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 743111791) ^ 371555895 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 743111791) ^ 247703930 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 743111791) ^ 148622358 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 743111791) ^ 6944970 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 743111791) ^ 4105590 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 743111791) ^ 581010 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_867114133 : Nat.Prime 867114133 := by
  apply lucas_primality 867114133 (5 : ZMod 867114133)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (307, 1), (4441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (307, 1), (4441, 1)] : List FactorBlock).map factorBlockValue).prod) = 867114133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_53
      · exact prime_seventyFiveBU_307
      · exact prime_seventyFiveBU_4441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 867114133) ^ 433557066 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 867114133) ^ 289038044 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 867114133) ^ 16360644 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 867114133) ^ 2824476 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 867114133) ^ 195252 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1029402103 : Nat.Prime 1029402103 := by
  apply lucas_primality 1029402103 (3 : ZMod 1029402103)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1069, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1069, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1029402103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_1069
      · exact prime_seventyFiveBU_8447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1029402103) ^ 514701051 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029402103) ^ 343134034 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029402103) ^ 54179058 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029402103) ^ 962958 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029402103) ^ 121866 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1098245609 : Nat.Prime 1098245609 := by
  apply lucas_primality 1098245609 (3 : ZMod 1098245609)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (523, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (523, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1098245609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_71
      · exact prime_seventyFiveBU_523
      · exact prime_seventyFiveBU_3697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1098245609) ^ 549122804 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098245609) ^ 15468248 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098245609) ^ 2099896 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098245609) ^ 297064 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1265864983 : Nat.Prime 1265864983 := by
  apply lucas_primality 1265864983 (11 : ZMod 1265864983)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (12410441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (12410441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1265864983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_12410441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1265864983) ^ 632932491 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1265864983) ^ 421954994 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1265864983) ^ 74462646 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1265864983) ^ 102 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1366253183 : Nat.Prime 1366253183 := by
  apply lucas_primality 1366253183 (5 : ZMod 1366253183)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (103, 1), (135353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (103, 1), (135353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366253183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_103
      · exact prime_seventyFiveBU_135353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1366253183) ^ 683126591 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1366253183) ^ 195179026 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1366253183) ^ 13264594 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1366253183) ^ 10094 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1849226593 : Nat.Prime 1849226593 := by
  apply lucas_primality 1849226593 (5 : ZMod 1849226593)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (3539, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (3539, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1849226593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_3539
      · exact prime_seventyFiveBU_5443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1849226593) ^ 924613296 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1849226593) ^ 616408864 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1849226593) ^ 522528 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1849226593) ^ 339744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1903046813 : Nat.Prime 1903046813 := by
  apply lucas_primality 1903046813 (2 : ZMod 1903046813)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5807, 1), (81929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5807, 1), (81929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1903046813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5807
      · exact prime_seventyFiveBU_81929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1903046813) ^ 951523406 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1903046813) ^ 327716 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1903046813) ^ 23228 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2054171213 : Nat.Prime 2054171213 := by
  apply lucas_primality 2054171213 (2 : ZMod 2054171213)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (241, 1), (1381, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (241, 1), (1381, 1), (1543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2054171213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_241
      · exact prime_seventyFiveBU_1381
      · exact prime_seventyFiveBU_1543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2054171213) ^ 1027085606 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054171213) ^ 8523532 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054171213) ^ 1487452 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054171213) ^ 1331284 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2187694681 : Nat.Prime 2187694681 := by
  apply lucas_primality 2187694681 (11 : ZMod 2187694681)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (792643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (792643, 1)] : List FactorBlock).map factorBlockValue).prod) = 2187694681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_792643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2187694681) ^ 1093847340 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2187694681) ^ 729231560 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2187694681) ^ 437538936 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2187694681) ^ 95117160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2187694681) ^ 2760 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2271423983 : Nat.Prime 2271423983 := by
  apply lucas_primality 2271423983 (5 : ZMod 2271423983)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (13683277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (13683277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2271423983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_83
      · exact prime_seventyFiveBU_13683277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2271423983) ^ 1135711991 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2271423983) ^ 27366554 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2271423983) ^ 166 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2344345193 : Nat.Prime 2344345193 := by
  apply lucas_primality 2344345193 (3 : ZMod 2344345193)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41863307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41863307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2344345193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_41863307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2344345193) ^ 1172172596 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2344345193) ^ 334906456 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2344345193) ^ 56 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2373890569 : Nat.Prime 2373890569 := by
  apply lucas_primality 2373890569 (11 : ZMod 2373890569)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (269, 1), (52529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (269, 1), (52529, 1)] : List FactorBlock).map factorBlockValue).prod) = 2373890569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_269
      · exact prime_seventyFiveBU_52529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2373890569) ^ 1186945284 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2373890569) ^ 791296856 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2373890569) ^ 339127224 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2373890569) ^ 8824872 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2373890569) ^ 45192 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2484508661 : Nat.Prime 2484508661 := by
  apply lucas_primality 2484508661 (2 : ZMod 2484508661)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1279, 1), (97127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1279, 1), (97127, 1)] : List FactorBlock).map factorBlockValue).prod) = 2484508661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_1279
      · exact prime_seventyFiveBU_97127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2484508661) ^ 1242254330 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2484508661) ^ 496901732 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2484508661) ^ 1942540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2484508661) ^ 25580 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3002140217 : Nat.Prime 3002140217 := by
  apply lucas_primality 3002140217 (3 : ZMod 3002140217)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (18287, 1), (20521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (18287, 1), (20521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3002140217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_18287
      · exact prime_seventyFiveBU_20521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3002140217) ^ 1501070108 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3002140217) ^ 164168 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3002140217) ^ 146296 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3151525759 : Nat.Prime 3151525759 := by
  apply lucas_primality 3151525759 (6 : ZMod 3151525759)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (18112217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (18112217, 1)] : List FactorBlock).map factorBlockValue).prod) = 3151525759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_18112217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3151525759) ^ 1575762879 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3151525759) ^ 1050508586 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3151525759) ^ 108673302 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3151525759) ^ 174 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3626964073 : Nat.Prime 3626964073 := by
  apply lucas_primality 3626964073 (7 : ZMod 3626964073)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (613, 1), (2221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (613, 1), (2221, 1)] : List FactorBlock).map factorBlockValue).prod) = 3626964073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_613
      · exact prime_seventyFiveBU_2221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3626964073) ^ 1813482036 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3626964073) ^ 1208988024 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3626964073) ^ 98026056 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3626964073) ^ 5916744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3626964073) ^ 1633032 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4548643271 : Nat.Prime 4548643271 := by
  apply lucas_primality 4548643271 (7 : ZMod 4548643271)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (454864327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (454864327, 1)] : List FactorBlock).map factorBlockValue).prod) = 4548643271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_454864327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4548643271) ^ 2274321635 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4548643271) ^ 909728654 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4548643271) ^ 10 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4666011787 : Nat.Prime 4666011787 := by
  apply lucas_primality 4666011787 (2 : ZMod 4666011787)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (227, 1), (26557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (227, 1), (26557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4666011787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_227
      · exact prime_seventyFiveBU_26557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4666011787) ^ 2333005893 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4666011787) ^ 1555337262 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4666011787) ^ 108511902 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4666011787) ^ 20555118 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4666011787) ^ 175698 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5620179863 : Nat.Prime 5620179863 := by
  apply lucas_primality 5620179863 (7 : ZMod 5620179863)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (255462721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (255462721, 1)] : List FactorBlock).map factorBlockValue).prod) = 5620179863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_255462721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5620179863) ^ 2810089931 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5620179863) ^ 510925442 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 5620179863) ^ 22 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5744412511 : Nat.Prime 5744412511 := by
  apply lucas_primality 5744412511 (3 : ZMod 5744412511)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (179, 1), (36887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (179, 1), (36887, 1)] : List FactorBlock).map factorBlockValue).prod) = 5744412511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_179
      · exact prime_seventyFiveBU_36887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5744412511) ^ 2872206255 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5744412511) ^ 1914804170 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5744412511) ^ 1148882502 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5744412511) ^ 198083190 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5744412511) ^ 32091690 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 5744412511) ^ 155730 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5993717063 : Nat.Prime 5993717063 := by
  apply lucas_primality 5993717063 (5 : ZMod 5993717063)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (211, 1), (26849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (211, 1), (26849, 1)] : List FactorBlock).map factorBlockValue).prod) = 5993717063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_211
      · exact prime_seventyFiveBU_26849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5993717063) ^ 2996858531 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5993717063) ^ 260596394 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5993717063) ^ 28406242 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5993717063) ^ 223238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_8944285153 : Nat.Prime 8944285153 := by
  apply lucas_primality 8944285153 (7 : ZMod 8944285153)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 2), (769997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 2), (769997, 1)] : List FactorBlock).map factorBlockValue).prod) = 8944285153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_769997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8944285153) ^ 4472142576 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 8944285153) ^ 2981428384 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 8944285153) ^ 813116832 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 8944285153) ^ 11616 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_9526075261 : Nat.Prime 9526075261 := by
  apply lucas_primality 9526075261 (7 : ZMod 9526075261)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (12212917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (12212917, 1)] : List FactorBlock).map factorBlockValue).prod) = 9526075261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_12212917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9526075261) ^ 4763037630 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9526075261) ^ 3175358420 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9526075261) ^ 1905215052 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9526075261) ^ 732775020 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9526075261) ^ 780 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_10699515667 : Nat.Prime 10699515667 := by
  apply lucas_primality 10699515667 (29 : ZMod 10699515667)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (9435199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (9435199, 1)] : List FactorBlock).map factorBlockValue).prod) = 10699515667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_9435199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 10699515667) ^ 5349757833 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 10699515667) ^ 3566505222 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 10699515667) ^ 1528502238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 10699515667) ^ 1134 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_11041194601 : Nat.Prime 11041194601 := by
  apply lucas_primality 11041194601 (7 : ZMod 11041194601)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (6133997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (6133997, 1)] : List FactorBlock).map factorBlockValue).prod) = 11041194601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_6133997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 11041194601) ^ 5520597300 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 11041194601) ^ 3680398200 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 11041194601) ^ 2208238920 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 11041194601) ^ 1800 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_11987434127 : Nat.Prime 11987434127 := by
  apply lucas_primality 11987434127 (5 : ZMod 11987434127)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5993717063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5993717063, 1)] : List FactorBlock).map factorBlockValue).prod) = 11987434127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5993717063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 11987434127) ^ 5993717063 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11987434127) ^ 2 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_16827927169 : Nat.Prime 16827927169 := by
  apply lucas_primality 16827927169 (29 : ZMod 16827927169)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (41, 1), (82219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (41, 1), (82219, 1)] : List FactorBlock).map factorBlockValue).prod) = 16827927169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_82219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 16827927169) ^ 8413963584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 16827927169) ^ 5609309056 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 16827927169) ^ 1294455936 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 16827927169) ^ 410437248 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 16827927169) ^ 204672 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_17530341827 : Nat.Prime 17530341827 := by
  apply lucas_primality 17530341827 (2 : ZMod 17530341827)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1291, 1), (399379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1291, 1), (399379, 1)] : List FactorBlock).map factorBlockValue).prod) = 17530341827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_1291
      · exact prime_seventyFiveBU_399379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17530341827) ^ 8765170913 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17530341827) ^ 1031196578 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17530341827) ^ 13578886 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17530341827) ^ 43894 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_18798704059 : Nat.Prime 18798704059 := by
  apply lucas_primality 18798704059 (10 : ZMod 18798704059)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14369, 1), (218047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14369, 1), (218047, 1)] : List FactorBlock).map factorBlockValue).prod) = 18798704059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_14369
      · exact prime_seventyFiveBU_218047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 18798704059) ^ 9399352029 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 18798704059) ^ 6266234686 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 18798704059) ^ 1308282 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 18798704059) ^ 86214 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_24352508821 : Nat.Prime 24352508821 := by
  apply lucas_primality 24352508821 (6 : ZMod 24352508821)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1109, 1), (365983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1109, 1), (365983, 1)] : List FactorBlock).map factorBlockValue).prod) = 24352508821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_1109
      · exact prime_seventyFiveBU_365983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 24352508821) ^ 12176254410 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 24352508821) ^ 8117502940 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 24352508821) ^ 4870501764 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 24352508821) ^ 21958980 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 24352508821) ^ 66540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_27577801403 : Nat.Prime 27577801403 := by
  apply lucas_primality 27577801403 (2 : ZMod 27577801403)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (281, 1), (312553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (281, 1), (312553, 1)] : List FactorBlock).map factorBlockValue).prod) = 27577801403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_157
      · exact prime_seventyFiveBU_281
      · exact prime_seventyFiveBU_312553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27577801403) ^ 13788900701 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27577801403) ^ 175654786 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27577801403) ^ 98141642 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27577801403) ^ 88234 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_34134987209 : Nat.Prime 34134987209 := by
  apply lucas_primality 34134987209 (3 : ZMod 34134987209)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (17, 1), (5122297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (17, 1), (5122297, 1)] : List FactorBlock).map factorBlockValue).prod) = 34134987209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_5122297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34134987209) ^ 17067493604 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34134987209) ^ 4876426744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34134987209) ^ 2007940424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 34134987209) ^ 6664 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_45428479661 : Nat.Prime 45428479661 := by
  apply lucas_primality 45428479661 (2 : ZMod 45428479661)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2271423983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2271423983, 1)] : List FactorBlock).map factorBlockValue).prod) = 45428479661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_2271423983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45428479661) ^ 22714239830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45428479661) ^ 9085695932 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 45428479661) ^ 20 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_54850141189 : Nat.Prime 54850141189 := by
  apply lucas_primality 54850141189 (2 : ZMod 54850141189)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1171, 1), (1301123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1171, 1), (1301123, 1)] : List FactorBlock).map factorBlockValue).prod) = 54850141189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1171
      · exact prime_seventyFiveBU_1301123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54850141189) ^ 27425070594 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 54850141189) ^ 18283380396 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 54850141189) ^ 46840428 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 54850141189) ^ 42156 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_56947195463 : Nat.Prime 56947195463 := by
  apply lucas_primality 56947195463 (5 : ZMod 56947195463)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2969, 1), (9590299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2969, 1), (9590299, 1)] : List FactorBlock).map factorBlockValue).prod) = 56947195463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_2969
      · exact prime_seventyFiveBU_9590299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 56947195463) ^ 28473597731 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56947195463) ^ 19180598 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56947195463) ^ 5938 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_68269974419 : Nat.Prime 68269974419 := by
  apply lucas_primality 68269974419 (2 : ZMod 68269974419)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34134987209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34134987209, 1)] : List FactorBlock).map factorBlockValue).prod) = 68269974419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_34134987209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 68269974419) ^ 34134987209 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68269974419) ^ 2 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_71216717071 : Nat.Prime 71216717071 := by
  apply lucas_primality 71216717071 (15 : ZMod 71216717071)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2373890569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2373890569, 1)] : List FactorBlock).map factorBlockValue).prod) = 71216717071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_2373890569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 71216717071) ^ 35608358535 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 71216717071) ^ 23738905690 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 71216717071) ^ 14243343414 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 71216717071) ^ 30 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_107782593181 : Nat.Prime 107782593181 := by
  apply lucas_primality 107782593181 (2 : ZMod 107782593181)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (83, 1), (367, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (83, 1), (367, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 107782593181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_83
      · exact prime_seventyFiveBU_367
      · exact prime_seventyFiveBU_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107782593181) ^ 53891296590 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 35927531060 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 21556518636 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 6340152540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 1298585460 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 293685540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107782593181) ^ 31070220 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_122580177553 : Nat.Prime 122580177553 := by
  apply lucas_primality 122580177553 (5 : ZMod 122580177553)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (59, 1), (107, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (59, 1), (107, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) = 122580177553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_59
      · exact prime_seventyFiveBU_107
      · exact prime_seventyFiveBU_6421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122580177553) ^ 61290088776 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 122580177553) ^ 40860059184 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 122580177553) ^ 17511453936 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 122580177553) ^ 2077630128 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 122580177553) ^ 1145609136 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 122580177553) ^ 19090512 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_122995461353 : Nat.Prime 122995461353 := by
  apply lucas_primality 122995461353 (3 : ZMod 122995461353)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109, 1), (173, 1), (815317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109, 1), (173, 1), (815317, 1)] : List FactorBlock).map factorBlockValue).prod) = 122995461353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_109
      · exact prime_seventyFiveBU_173
      · exact prime_seventyFiveBU_815317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 122995461353) ^ 61497730676 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 122995461353) ^ 1128398728 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 122995461353) ^ 710956424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 122995461353) ^ 150856 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_145843000271 : Nat.Prime 145843000271 := by
  apply lucas_primality 145843000271 (11 : ZMod 145843000271)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (37, 1), (5011, 1), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (37, 1), (5011, 1), (7151, 1)] : List FactorBlock).map factorBlockValue).prod) = 145843000271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_5011
      · exact prime_seventyFiveBU_7151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 145843000271) ^ 72921500135 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 145843000271) ^ 29168600054 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 145843000271) ^ 13258454570 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 145843000271) ^ 3941702710 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 145843000271) ^ 29104570 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 145843000271) ^ 20394770 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_156926521291 : Nat.Prime 156926521291 := by
  apply lucas_primality 156926521291 (13 : ZMod 156926521291)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (23, 1), (773, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (23, 1), (773, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 156926521291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_773
      · exact prime_seventyFiveBU_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 156926521291) ^ 78463260645 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 52308840430 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 31385304258 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 22418074470 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 14266047390 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 6822892230 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 203009730 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 156926521291) ^ 41069490 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_177429175481 : Nat.Prime 177429175481 := by
  apply lucas_primality 177429175481 (3 : ZMod 177429175481)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (94377221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (94377221, 1)] : List FactorBlock).map factorBlockValue).prod) = 177429175481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_47
      · exact prime_seventyFiveBU_94377221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 177429175481) ^ 88714587740 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 177429175481) ^ 35485835096 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 177429175481) ^ 3775088840 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 177429175481) ^ 1880 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_185973583519 : Nat.Prime 185973583519 := by
  apply lucas_primality 185973583519 (21 : ZMod 185973583519)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (96559493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (96559493, 1)] : List FactorBlock).map factorBlockValue).prod) = 185973583519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_107
      · exact prime_seventyFiveBU_96559493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 185973583519) ^ 92986791759 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (21 : ZMod 185973583519) ^ 61991194506 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (21 : ZMod 185973583519) ^ 1738070874 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (21 : ZMod 185973583519) ^ 1926 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_189603044747 : Nat.Prime 189603044747 := by
  apply lucas_primality 189603044747 (2 : ZMod 189603044747)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (17321, 1), (133493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (17321, 1), (133493, 1)] : List FactorBlock).map factorBlockValue).prod) = 189603044747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_17321
      · exact prime_seventyFiveBU_133493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 189603044747) ^ 94801522373 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 189603044747) ^ 4624464506 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 189603044747) ^ 10946426 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 189603044747) ^ 1420322 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_191545661413 : Nat.Prime 191545661413 := by
  apply lucas_primality 191545661413 (2 : ZMod 191545661413)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (84455759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (84455759, 1)] : List FactorBlock).map factorBlockValue).prod) = 191545661413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_84455759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191545661413) ^ 95772830706 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191545661413) ^ 63848553804 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191545661413) ^ 27363665916 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191545661413) ^ 2268 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_236951551891 : Nat.Prime 236951551891 := by
  apply lucas_primality 236951551891 (3 : ZMod 236951551891)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 2), (1381, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 2), (1381, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) = 236951551891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_1381
      · exact prime_seventyFiveBU_5281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 236951551891) ^ 118475775945 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 236951551891) ^ 78983850630 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 236951551891) ^ 47390310378 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 236951551891) ^ 12471134310 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 236951551891) ^ 171579690 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 236951551891) ^ 44868690 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_240467468921 : Nat.Prime 240467468921 := by
  apply lucas_primality 240467468921 (3 : ZMod 240467468921)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (1487, 1), (577547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (1487, 1), (577547, 1)] : List FactorBlock).map factorBlockValue).prod) = 240467468921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_1487
      · exact prime_seventyFiveBU_577547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 240467468921) ^ 120233734460 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 240467468921) ^ 48093493784 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 240467468921) ^ 34352495560 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 240467468921) ^ 161713160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 240467468921) ^ 416360 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_272570877967 : Nat.Prime 272570877967 := by
  apply lucas_primality 272570877967 (5 : ZMod 272570877967)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (45428479661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (45428479661, 1)] : List FactorBlock).map factorBlockValue).prod) = 272570877967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_45428479661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 272570877967) ^ 136285438983 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 272570877967) ^ 90856959322 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 272570877967) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_383914758287 : Nat.Prime 383914758287 := by
  apply lucas_primality 383914758287 (5 : ZMod 383914758287)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52301, 1), (3670243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52301, 1), (3670243, 1)] : List FactorBlock).map factorBlockValue).prod) = 383914758287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_52301
      · exact prime_seventyFiveBU_3670243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 383914758287) ^ 191957379143 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 383914758287) ^ 7340486 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 383914758287) ^ 104602 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_388452578161 : Nat.Prime 388452578161 := by
  apply lucas_primality 388452578161 (11 : ZMod 388452578161)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (10883, 1), (148723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (10883, 1), (148723, 1)] : List FactorBlock).map factorBlockValue).prod) = 388452578161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_10883
      · exact prime_seventyFiveBU_148723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 388452578161) ^ 194226289080 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 388452578161) ^ 129484192720 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 388452578161) ^ 77690515632 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 388452578161) ^ 35693520 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 388452578161) ^ 2611920 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_472459378991 : Nat.Prime 472459378991 := by
  apply lucas_primality 472459378991 (23 : ZMod 472459378991)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (2054171213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (2054171213, 1)] : List FactorBlock).map factorBlockValue).prod) = 472459378991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_2054171213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 472459378991) ^ 236229689495 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (23 : ZMod 472459378991) ^ 94491875798 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (23 : ZMod 472459378991) ^ 20541712130 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (23 : ZMod 472459378991) ^ 230 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_571564515661 : Nat.Prime 571564515661 := by
  apply lucas_primality 571564515661 (2 : ZMod 571564515661)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (9526075261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (9526075261, 1)] : List FactorBlock).map factorBlockValue).prod) = 571564515661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_9526075261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 571564515661) ^ 285782257830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 571564515661) ^ 190521505220 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 571564515661) ^ 114312903132 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 571564515661) ^ 60 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_628720839077 : Nat.Prime 628720839077 := by
  apply lucas_primality 628720839077 (2 : ZMod 628720839077)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (127, 1), (181, 1), (621617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (127, 1), (181, 1), (621617, 1)] : List FactorBlock).map factorBlockValue).prod) = 628720839077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_127
      · exact prime_seventyFiveBU_181
      · exact prime_seventyFiveBU_621617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 628720839077) ^ 314360419538 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 628720839077) ^ 57156439916 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 628720839077) ^ 4950557788 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 628720839077) ^ 3473595796 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 628720839077) ^ 1011428 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_678870472219 : Nat.Prime 678870472219 := by
  apply lucas_primality 678870472219 (2 : ZMod 678870472219)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (196873, 1), (574711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (196873, 1), (574711, 1)] : List FactorBlock).map factorBlockValue).prod) = 678870472219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_196873
      · exact prime_seventyFiveBU_574711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 678870472219) ^ 339435236109 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678870472219) ^ 226290157406 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678870472219) ^ 3448266 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678870472219) ^ 1181238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_689118392999 : Nat.Prime 689118392999 := by
  apply lucas_primality 689118392999 (7 : ZMod 689118392999)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (811, 1), (60693887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (811, 1), (60693887, 1)] : List FactorBlock).map factorBlockValue).prod) = 689118392999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_811
      · exact prime_seventyFiveBU_60693887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 689118392999) ^ 344559196499 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 689118392999) ^ 98445484714 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 689118392999) ^ 849714418 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 689118392999) ^ 11354 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_723660913903 : Nat.Prime 723660913903 := by
  apply lucas_primality 723660913903 (3 : ZMod 723660913903)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (17881, 1), (34949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (17881, 1), (34949, 1)] : List FactorBlock).map factorBlockValue).prod) = 723660913903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_193
      · exact prime_seventyFiveBU_17881
      · exact prime_seventyFiveBU_34949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 723660913903) ^ 361830456951 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 723660913903) ^ 241220304634 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 723660913903) ^ 3749538414 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 723660913903) ^ 40470942 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 723660913903) ^ 20706198 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_737972768119 : Nat.Prime 737972768119 := by
  apply lucas_primality 737972768119 (3 : ZMod 737972768119)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (122995461353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (122995461353, 1)] : List FactorBlock).map factorBlockValue).prod) = 737972768119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_122995461353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 737972768119) ^ 368986384059 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 737972768119) ^ 245990922706 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 737972768119) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_750233247103 : Nat.Prime 750233247103 := by
  apply lucas_primality 750233247103 (3 : ZMod 750233247103)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (2017, 1), (558491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (2017, 1), (558491, 1)] : List FactorBlock).map factorBlockValue).prod) = 750233247103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_2017
      · exact prime_seventyFiveBU_558491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 750233247103) ^ 375116623551 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 750233247103) ^ 250077749034 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 750233247103) ^ 20276574246 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 750233247103) ^ 371955006 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 750233247103) ^ 1343322 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_937389237703 : Nat.Prime 937389237703 := by
  apply lucas_primality 937389237703 (3 : ZMod 937389237703)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (2437, 1), (31721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (2437, 1), (31721, 1)] : List FactorBlock).map factorBlockValue).prod) = 937389237703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_47
      · exact prime_seventyFiveBU_2437
      · exact prime_seventyFiveBU_31721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 937389237703) ^ 468694618851 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 937389237703) ^ 312463079234 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 937389237703) ^ 21799749714 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 937389237703) ^ 19944451866 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 937389237703) ^ 384648846 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 937389237703) ^ 29551062 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1155331041079 : Nat.Prime 1155331041079 := by
  apply lucas_primality 1155331041079 (12 : ZMod 1155331041079)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (197, 1), (1429, 1), (15907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (197, 1), (1429, 1), (15907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1155331041079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_197
      · exact prime_seventyFiveBU_1429
      · exact prime_seventyFiveBU_15907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1155331041079) ^ 577665520539 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (12 : ZMod 1155331041079) ^ 385110347026 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (12 : ZMod 1155331041079) ^ 26868163746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (12 : ZMod 1155331041079) ^ 5864624574 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (12 : ZMod 1155331041079) ^ 808489182 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (12 : ZMod 1155331041079) ^ 72630354 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1185870667481 : Nat.Prime 1185870667481 := by
  apply lucas_primality 1185870667481 (3 : ZMod 1185870667481)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (56249, 1), (527063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (56249, 1), (527063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185870667481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_56249
      · exact prime_seventyFiveBU_527063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1185870667481) ^ 592935333740 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185870667481) ^ 237174133496 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185870667481) ^ 21082520 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1185870667481) ^ 2249960 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1286975486399 : Nat.Prime 1286975486399 := by
  apply lucas_primality 1286975486399 (7 : ZMod 1286975486399)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (2484508661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (2484508661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1286975486399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_2484508661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1286975486399) ^ 643487743199 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1286975486399) ^ 183853640914 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1286975486399) ^ 34783121254 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1286975486399) ^ 518 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1380711283967 : Nat.Prime 1380711283967 := by
  apply lucas_primality 1380711283967 (5 : ZMod 1380711283967)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103, 1), (233, 1), (4109431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103, 1), (233, 1), (4109431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380711283967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_103
      · exact prime_seventyFiveBU_233
      · exact prime_seventyFiveBU_4109431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1380711283967) ^ 690355641983 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1380711283967) ^ 197244469138 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1380711283967) ^ 13404963922 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1380711283967) ^ 5925799502 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1380711283967) ^ 335986 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1618319889119 : Nat.Prime 1618319889119 := by
  apply lucas_primality 1618319889119 (13 : ZMod 1618319889119)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23857, 1), (33917087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23857, 1), (33917087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1618319889119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_23857
      · exact prime_seventyFiveBU_33917087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1618319889119) ^ 809159944559 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1618319889119) ^ 67834174 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1618319889119) ^ 47714 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1635425267803 : Nat.Prime 1635425267803 := by
  apply lucas_primality 1635425267803 (5 : ZMod 1635425267803)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (272570877967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (272570877967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1635425267803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_272570877967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1635425267803) ^ 817712633901 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1635425267803) ^ 545141755934 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1635425267803) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1676382565489 : Nat.Prime 1676382565489 := by
  apply lucas_primality 1676382565489 (13 : ZMod 1676382565489)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1291, 1), (27052391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1291, 1), (27052391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1676382565489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1291
      · exact prime_seventyFiveBU_27052391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1676382565489) ^ 838191282744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1676382565489) ^ 558794188496 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1676382565489) ^ 1298514768 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1676382565489) ^ 61968 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1738995135803 : Nat.Prime 1738995135803 := by
  apply lucas_primality 1738995135803 (2 : ZMod 1738995135803)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14629, 1), (59436569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14629, 1), (59436569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1738995135803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_14629
      · exact prime_seventyFiveBU_59436569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1738995135803) ^ 869497567901 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1738995135803) ^ 118873138 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1738995135803) ^ 29258 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2157903806239 : Nat.Prime 2157903806239 := by
  apply lucas_primality 2157903806239 (11 : ZMod 2157903806239)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (173, 1), (349, 1), (38933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (173, 1), (349, 1), (38933, 1)] : List FactorBlock).map factorBlockValue).prod) = 2157903806239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_173
      · exact prime_seventyFiveBU_349
      · exact prime_seventyFiveBU_38933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2157903806239) ^ 1078951903119 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2157903806239) ^ 719301268746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2157903806239) ^ 126935518014 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2157903806239) ^ 12473432406 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2157903806239) ^ 6183105462 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2157903806239) ^ 55426086 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2238169845409 : Nat.Prime 2238169845409 := by
  apply lucas_primality 2238169845409 (29 : ZMod 2238169845409)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (73, 1), (45624793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (73, 1), (45624793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2238169845409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_73
      · exact prime_seventyFiveBU_45624793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 2238169845409) ^ 1119084922704 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 2238169845409) ^ 746056615136 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 2238169845409) ^ 319738549344 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 2238169845409) ^ 30659860896 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (29 : ZMod 2238169845409) ^ 49056 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2951891072477 : Nat.Prime 2951891072477 := by
  apply lucas_primality 2951891072477 (2 : ZMod 2951891072477)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (737972768119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (737972768119, 1)] : List FactorBlock).map factorBlockValue).prod) = 2951891072477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_737972768119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2951891072477) ^ 1475945536238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951891072477) ^ 4 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3362057505823 : Nat.Prime 3362057505823 := by
  apply lucas_primality 3362057505823 (3 : ZMod 3362057505823)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (659, 1), (12277, 1), (69259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (659, 1), (12277, 1), (69259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3362057505823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_659
      · exact prime_seventyFiveBU_12277
      · exact prime_seventyFiveBU_69259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3362057505823) ^ 1681028752911 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3362057505823) ^ 1120685835274 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3362057505823) ^ 5101756458 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3362057505823) ^ 273850086 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3362057505823) ^ 48543258 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3541604969557 : Nat.Prime 3541604969557 := by
  apply lucas_primality 3541604969557 (2 : ZMod 3541604969557)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (743, 1), (1489, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (743, 1), (1489, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) = 3541604969557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_743
      · exact prime_seventyFiveBU_1489
      · exact prime_seventyFiveBU_29641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3541604969557) ^ 1770802484778 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3541604969557) ^ 1180534989852 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3541604969557) ^ 4766628492 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3541604969557) ^ 2378512404 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3541604969557) ^ 119483316 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3608448510221 : Nat.Prime 3608448510221 := by
  apply lucas_primality 3608448510221 (2 : ZMod 3608448510221)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (353, 1), (523, 1), (977269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (353, 1), (523, 1), (977269, 1)] : List FactorBlock).map factorBlockValue).prod) = 3608448510221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_353
      · exact prime_seventyFiveBU_523
      · exact prime_seventyFiveBU_977269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3608448510221) ^ 1804224255110 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3608448510221) ^ 721689702044 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3608448510221) ^ 10222233740 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3608448510221) ^ 6899519140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3608448510221) ^ 3692380 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3842969394599 : Nat.Prime 3842969394599 := by
  apply lucas_primality 3842969394599 (11 : ZMod 3842969394599)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (123817, 1), (15518747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (123817, 1), (15518747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3842969394599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_123817
      · exact prime_seventyFiveBU_15518747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3842969394599) ^ 1921484697299 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 3842969394599) ^ 31037494 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 3842969394599) ^ 247634 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4341965483419 : Nat.Prime 4341965483419 := by
  apply lucas_primality 4341965483419 (2 : ZMod 4341965483419)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (723660913903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (723660913903, 1)] : List FactorBlock).map factorBlockValue).prod) = 4341965483419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_723660913903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4341965483419) ^ 2170982741709 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341965483419) ^ 1447321827806 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4341965483419) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4463366004457 : Nat.Prime 4463366004457 := by
  apply lucas_primality 4463366004457 (15 : ZMod 4463366004457)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (185973583519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (185973583519, 1)] : List FactorBlock).map factorBlockValue).prod) = 4463366004457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_185973583519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 4463366004457) ^ 2231683002228 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 4463366004457) ^ 1487788668152 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 4463366004457) ^ 24 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4757117181697 : Nat.Prime 4757117181697 := by
  apply lucas_primality 4757117181697 (5 : ZMod 4757117181697)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (11, 1), (131, 1), (151, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (11, 1), (131, 1), (151, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) = 4757117181697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_131
      · exact prime_seventyFiveBU_151
      · exact prime_seventyFiveBU_3163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4757117181697) ^ 2378558590848 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4757117181697) ^ 1585705727232 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4757117181697) ^ 432465198336 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4757117181697) ^ 36313871616 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4757117181697) ^ 31504087296 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4757117181697) ^ 1503988992 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_6658274905753 : Nat.Prime 6658274905753 := by
  apply lucas_primality 6658274905753 (15 : ZMod 6658274905753)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1601, 1), (173284273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1601, 1), (173284273, 1)] : List FactorBlock).map factorBlockValue).prod) = 6658274905753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1601
      · exact prime_seventyFiveBU_173284273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 6658274905753) ^ 3329137452876 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 6658274905753) ^ 2219424968584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 6658274905753) ^ 4158822552 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (15 : ZMod 6658274905753) ^ 38424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_7150106376953 : Nat.Prime 7150106376953 := by
  apply lucas_primality 7150106376953 (3 : ZMod 7150106376953)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (37, 1), (137, 1), (2289863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (37, 1), (137, 1), (2289863, 1)] : List FactorBlock).map factorBlockValue).prod) = 7150106376953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_137
      · exact prime_seventyFiveBU_2289863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7150106376953) ^ 3575053188476 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7150106376953) ^ 1021443768136 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7150106376953) ^ 650009670632 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7150106376953) ^ 193246118296 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7150106376953) ^ 52190557496 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 7150106376953) ^ 3122504 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_8530255868077 : Nat.Prime 8530255868077 := by
  apply lucas_primality 8530255868077 (2 : ZMod 8530255868077)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (236951551891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (236951551891, 1)] : List FactorBlock).map factorBlockValue).prod) = 8530255868077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_236951551891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8530255868077) ^ 4265127934038 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8530255868077) ^ 2843418622692 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8530255868077) ^ 36 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_10089758557217 : Nat.Prime 10089758557217 := by
  apply lucas_primality 10089758557217 (3 : ZMod 10089758557217)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (17, 1), (19, 1), (149, 1), (503963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (17, 1), (19, 1), (149, 1), (503963, 1)] : List FactorBlock).map factorBlockValue).prod) = 10089758557217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_149
      · exact prime_seventyFiveBU_503963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10089758557217) ^ 5044879278608 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089758557217) ^ 776135273632 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089758557217) ^ 593515209248 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089758557217) ^ 531039924064 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089758557217) ^ 67716500384 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089758557217) ^ 20020832 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_10295803891193 : Nat.Prime 10295803891193 := by
  apply lucas_primality 10295803891193 (3 : ZMod 10295803891193)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1286975486399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1286975486399, 1)] : List FactorBlock).map factorBlockValue).prod) = 10295803891193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_1286975486399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 10295803891193) ^ 5147901945596 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10295803891193) ^ 8 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_12219668499943 : Nat.Prime 12219668499943 := by
  apply lucas_primality 12219668499943 (3 : ZMod 12219668499943)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (678870472219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (678870472219, 1)] : List FactorBlock).map factorBlockValue).prod) = 12219668499943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_678870472219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12219668499943) ^ 6109834249971 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 12219668499943) ^ 4073222833314 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 12219668499943) ^ 18 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_12946559112953 : Nat.Prime 12946559112953 := by
  apply lucas_primality 12946559112953 (3 : ZMod 12946559112953)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1618319889119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1618319889119, 1)] : List FactorBlock).map factorBlockValue).prod) = 12946559112953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_1618319889119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 12946559112953) ^ 6473279556476 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 12946559112953) ^ 8 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_15358197113911 : Nat.Prime 15358197113911 := by
  apply lucas_primality 15358197113911 (7 : ZMod 15358197113911)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 2), (41, 1), (549019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 2), (41, 1), (549019, 1)] : List FactorBlock).map factorBlockValue).prod) = 15358197113911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_549019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15358197113911) ^ 7679098556955 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 5119399037970 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 3071639422782 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 2194028159130 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 808326163890 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 374590173510 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 15358197113911) ^ 27973890 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_20591607782387 : Nat.Prime 20591607782387 := by
  apply lucas_primality 20591607782387 (2 : ZMod 20591607782387)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10295803891193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10295803891193, 1)] : List FactorBlock).map factorBlockValue).prod) = 20591607782387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_10295803891193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20591607782387) ^ 10295803891193 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20591607782387) ^ 2 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_21249629817343 : Nat.Prime 21249629817343 := by
  apply lucas_primality 21249629817343 (3 : ZMod 21249629817343)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3541604969557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3541604969557, 1)] : List FactorBlock).map factorBlockValue).prod) = 21249629817343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_3541604969557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21249629817343) ^ 10624814908671 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21249629817343) ^ 7083209939114 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21249629817343) ^ 6 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_23717413349621 : Nat.Prime 23717413349621 := by
  apply lucas_primality 23717413349621 (2 : ZMod 23717413349621)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1185870667481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1185870667481, 1)] : List FactorBlock).map factorBlockValue).prod) = 23717413349621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_1185870667481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23717413349621) ^ 11858706674810 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 23717413349621) ^ 4743482669924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 23717413349621) ^ 20 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_24848613862087 : Nat.Prime 24848613862087 := by
  apply lucas_primality 24848613862087 (5 : ZMod 24848613862087)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (17, 1), (10789, 1), (460813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (17, 1), (10789, 1), (460813, 1)] : List FactorBlock).map factorBlockValue).prod) = 24848613862087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_10789
      · exact prime_seventyFiveBU_460813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24848613862087) ^ 12424306931043 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 24848613862087) ^ 8282871287362 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 24848613862087) ^ 3549801980298 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 24848613862087) ^ 1461683168358 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 24848613862087) ^ 2303143374 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 24848613862087) ^ 53923422 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_25939439011351 : Nat.Prime 25939439011351 := by
  apply lucas_primality 25939439011351 (3 : ZMod 25939439011351)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (2339, 1), (24644377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (2339, 1), (24644377, 1)] : List FactorBlock).map factorBlockValue).prod) = 25939439011351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_2339
      · exact prime_seventyFiveBU_24644377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25939439011351) ^ 12969719505675 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25939439011351) ^ 8646479670450 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25939439011351) ^ 5187887802270 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25939439011351) ^ 11089969650 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25939439011351) ^ 1052550 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_26457725223497 : Nat.Prime 26457725223497 := by
  apply lucas_primality 26457725223497 (3 : ZMod 26457725223497)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (472459378991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (472459378991, 1)] : List FactorBlock).map factorBlockValue).prod) = 26457725223497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_472459378991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26457725223497) ^ 13228862611748 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26457725223497) ^ 3779675031928 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26457725223497) ^ 56 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_40950029663377 : Nat.Prime 40950029663377 := by
  apply lucas_primality 40950029663377 (5 : ZMod 40950029663377)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (233, 1), (21517, 1), (170167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (233, 1), (21517, 1), (170167, 1)] : List FactorBlock).map factorBlockValue).prod) = 40950029663377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_233
      · exact prime_seventyFiveBU_21517
      · exact prime_seventyFiveBU_170167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40950029663377) ^ 20475014831688 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40950029663377) ^ 13650009887792 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40950029663377) ^ 175751200272 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40950029663377) ^ 1903147728 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40950029663377) ^ 240646128 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_46115632735189 : Nat.Prime 46115632735189 := by
  apply lucas_primality 46115632735189 (2 : ZMod 46115632735189)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3842969394599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3842969394599, 1)] : List FactorBlock).map factorBlockValue).prod) = 46115632735189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_3842969394599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46115632735189) ^ 23057816367594 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46115632735189) ^ 15371877578396 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46115632735189) ^ 12 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_46231340094211 : Nat.Prime 46231340094211 := by
  apply lucas_primality 46231340094211 (3 : ZMod 46231340094211)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (14207, 1), (108470801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (14207, 1), (108470801, 1)] : List FactorBlock).map factorBlockValue).prod) = 46231340094211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_14207
      · exact prime_seventyFiveBU_108470801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46231340094211) ^ 23115670047105 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46231340094211) ^ 15410446698070 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46231340094211) ^ 9246268018842 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46231340094211) ^ 3254124030 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46231340094211) ^ 426210 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_59275376359847 : Nat.Prime 59275376359847 := by
  apply lucas_primality 59275376359847 (5 : ZMod 59275376359847)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (113, 1), (24971, 1), (126547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (113, 1), (24971, 1), (126547, 1)] : List FactorBlock).map factorBlockValue).prod) = 59275376359847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_83
      · exact prime_seventyFiveBU_113
      · exact prime_seventyFiveBU_24971
      · exact prime_seventyFiveBU_126547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 59275376359847) ^ 29637688179923 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 59275376359847) ^ 714161160962 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 59275376359847) ^ 524560852742 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 59275376359847) ^ 2373768626 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 59275376359847) ^ 468406018 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_85695284919917 : Nat.Prime 85695284919917 := by
  apply lucas_primality 85695284919917 (2 : ZMod 85695284919917)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (70489, 1), (43418773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (70489, 1), (43418773, 1)] : List FactorBlock).map factorBlockValue).prod) = 85695284919917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_70489
      · exact prime_seventyFiveBU_43418773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85695284919917) ^ 42847642459958 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 85695284919917) ^ 12242183559988 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 85695284919917) ^ 1215725644 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 85695284919917) ^ 1973692 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_102240402499577 : Nat.Prime 102240402499577 := by
  apply lucas_primality 102240402499577 (3 : ZMod 102240402499577)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (81749, 1), (14212073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (81749, 1), (14212073, 1)] : List FactorBlock).map factorBlockValue).prod) = 102240402499577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_81749
      · exact prime_seventyFiveBU_14212073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102240402499577) ^ 51120201249788 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102240402499577) ^ 9294582045416 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102240402499577) ^ 1250662424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102240402499577) ^ 7193912 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_112385525820097 : Nat.Prime 112385525820097 := by
  apply lucas_primality 112385525820097 (5 : ZMod 112385525820097)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (41, 1), (241, 1), (59239073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (41, 1), (241, 1), (59239073, 1)] : List FactorBlock).map factorBlockValue).prod) = 112385525820097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_241
      · exact prime_seventyFiveBU_59239073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 112385525820097) ^ 56192762910048 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 112385525820097) ^ 37461841940032 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 112385525820097) ^ 2741110385856 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 112385525820097) ^ 466329982656 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 112385525820097) ^ 1897152 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_163150082827621 : Nat.Prime 163150082827621 := by
  apply lucas_primality 163150082827621 (6 : ZMod 163150082827621)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (388452578161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (388452578161, 1)] : List FactorBlock).map factorBlockValue).prod) = 163150082827621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_388452578161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 163150082827621) ^ 81575041413810 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 163150082827621) ^ 54383360942540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 163150082827621) ^ 32630016565524 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 163150082827621) ^ 23307154689660 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 163150082827621) ^ 420 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_209150045840353 : Nat.Prime 209150045840353 := by
  apply lucas_primality 209150045840353 (5 : ZMod 209150045840353)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (79, 1), (27577801403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (79, 1), (27577801403, 1)] : List FactorBlock).map factorBlockValue).prod) = 209150045840353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_79
      · exact prime_seventyFiveBU_27577801403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 209150045840353) ^ 104575022920176 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 209150045840353) ^ 69716681946784 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 209150045840353) ^ 2647468934688 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 209150045840353) ^ 7584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_297824618375789 : Nat.Prime 297824618375789 := by
  apply lucas_primality 297824618375789 (3 : ZMod 297824618375789)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (94151, 1), (2627297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (94151, 1), (2627297, 1)] : List FactorBlock).map factorBlockValue).prod) = 297824618375789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_94151
      · exact prime_seventyFiveBU_2627297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 297824618375789) ^ 148912309187894 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 297824618375789) ^ 42546374053684 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 297824618375789) ^ 6926153915716 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 297824618375789) ^ 3163265588 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 297824618375789) ^ 113357804 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_313414062221797 : Nat.Prime 313414062221797 := by
  apply lucas_primality 313414062221797 (2 : ZMod 313414062221797)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (14627, 1), (61572101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (14627, 1), (61572101, 1)] : List FactorBlock).map factorBlockValue).prod) = 313414062221797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_14627
      · exact prime_seventyFiveBU_61572101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313414062221797) ^ 156707031110898 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 313414062221797) ^ 104471354073932 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 313414062221797) ^ 10807381455924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 313414062221797) ^ 21427091148 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 313414062221797) ^ 5090196 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_349104161751497 : Nat.Prime 349104161751497 := by
  apply lucas_primality 349104161751497 (3 : ZMod 349104161751497)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (9619, 1), (67711169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (9619, 1), (67711169, 1)] : List FactorBlock).map factorBlockValue).prod) = 349104161751497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_67
      · exact prime_seventyFiveBU_9619
      · exact prime_seventyFiveBU_67711169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 349104161751497) ^ 174552080875748 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 349104161751497) ^ 5210509876888 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 349104161751497) ^ 36293186584 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 349104161751497) ^ 5155784 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_429276877184483 : Nat.Prime 429276877184483 := by
  apply lucas_primality 429276877184483 (2 : ZMod 429276877184483)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (960737, 1), (2169031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (960737, 1), (2169031, 1)] : List FactorBlock).map factorBlockValue).prod) = 429276877184483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_103
      · exact prime_seventyFiveBU_960737
      · exact prime_seventyFiveBU_2169031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 429276877184483) ^ 214638438592241 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429276877184483) ^ 4167736671694 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429276877184483) ^ 446820386 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429276877184483) ^ 197911822 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_434355374166557 : Nat.Prime 434355374166557 := by
  apply lucas_primality 434355374166557 (2 : ZMod 434355374166557)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1031, 1), (8693, 1), (12115933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1031, 1), (8693, 1), (12115933, 1)] : List FactorBlock).map factorBlockValue).prod) = 434355374166557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_1031
      · exact prime_seventyFiveBU_8693
      · exact prime_seventyFiveBU_12115933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 434355374166557) ^ 217177687083278 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 434355374166557) ^ 421295222276 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 434355374166557) ^ 49966107692 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 434355374166557) ^ 35849932 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_566912414271779 : Nat.Prime 566912414271779 := by
  apply lucas_primality 566912414271779 (2 : ZMod 566912414271779)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (1738995135803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (1738995135803, 1)] : List FactorBlock).map factorBlockValue).prod) = 566912414271779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_163
      · exact prime_seventyFiveBU_1738995135803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 566912414271779) ^ 283456207135889 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 566912414271779) ^ 3477990271606 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 566912414271779) ^ 326 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_571602087046513 : Nat.Prime 571602087046513 := by
  apply lucas_primality 571602087046513 (10 : ZMod 571602087046513)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (163, 1), (24352508821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (163, 1), (24352508821, 1)] : List FactorBlock).map factorBlockValue).prod) = 571602087046513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_163
      · exact prime_seventyFiveBU_24352508821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 571602087046513) ^ 285801043523256 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 571602087046513) ^ 190534029015504 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 571602087046513) ^ 3506761270224 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 571602087046513) ^ 23472 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_606458336983747 : Nat.Prime 606458336983747 := by
  apply lucas_primality 606458336983747 (2 : ZMod 606458336983747)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 2), (31, 1), (2677, 1), (177109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 2), (31, 1), (2677, 1), (177109, 1)] : List FactorBlock).map factorBlockValue).prod) = 606458336983747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_31
      · exact prime_seventyFiveBU_2677
      · exact prime_seventyFiveBU_177109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 606458336983747) ^ 303229168491873 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 202152778994582 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 46650641306442 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 26367753781902 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 19563172160766 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 226544018298 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 606458336983747) ^ 3424209594 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1110836485880647 : Nat.Prime 1110836485880647 := by
  apply lucas_primality 1110836485880647 (3 : ZMod 1110836485880647)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (773, 1), (1013, 1), (2683, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (773, 1), (1013, 1), (2683, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110836485880647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_773
      · exact prime_seventyFiveBU_1013
      · exact prime_seventyFiveBU_2683
      · exact prime_seventyFiveBU_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1110836485880647) ^ 555418242940323 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 370278828626882 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 158690926554378 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 1437045906702 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 1096580933742 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 414027762162 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110836485880647) ^ 88238659614 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1115220963141559 : Nat.Prime 1115220963141559 := by
  apply lucas_primality 1115220963141559 (3 : ZMod 1115220963141559)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (17, 1), (37, 1), (131, 1), (739, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (17, 1), (37, 1), (131, 1), (739, 1), (3727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115220963141559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_131
      · exact prime_seventyFiveBU_739
      · exact prime_seventyFiveBU_3727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1115220963141559) ^ 557610481570779 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 371740321047186 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 159317280448794 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 85786227933966 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 65601233125974 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 30141107111934 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 8513137123218 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 1509094672722 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115220963141559) ^ 299227518954 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1133824828543559 : Nat.Prime 1133824828543559 := by
  apply lucas_primality 1133824828543559 (11 : ZMod 1133824828543559)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (566912414271779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (566912414271779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133824828543559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_566912414271779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 1133824828543559) ^ 566912414271779 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1133824828543559) ^ 2 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1326233695470251 : Nat.Prime 1326233695470251 := by
  apply lucas_primality 1326233695470251 (6 : ZMod 1326233695470251)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (1933, 1), (14489, 1), (27059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (1933, 1), (14489, 1), (27059, 1)] : List FactorBlock).map factorBlockValue).prod) = 1326233695470251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_1933
      · exact prime_seventyFiveBU_14489
      · exact prime_seventyFiveBU_27059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1326233695470251) ^ 663116847735125 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1326233695470251) ^ 265246739094050 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1326233695470251) ^ 189461956495750 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1326233695470251) ^ 686101239250 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1326233695470251) ^ 91533832250 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1326233695470251) ^ 49012664750 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2195500034418947 : Nat.Prime 2195500034418947 := by
  apply lucas_primality 2195500034418947 (2 : ZMod 2195500034418947)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1265981, 1), (867114133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1265981, 1), (867114133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2195500034418947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_1265981
      · exact prime_seventyFiveBU_867114133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2195500034418947) ^ 1097750017209473 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2195500034418947) ^ 1734228266 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2195500034418947) ^ 2531962 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2273404837510621 : Nat.Prime 2273404837510621 := by
  apply lucas_primality 2273404837510621 (2 : ZMod 2273404837510621)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (11, 1), (36083, 1), (3535627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (11, 1), (36083, 1), (3535627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273404837510621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_36083
      · exact prime_seventyFiveBU_3535627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2273404837510621) ^ 1136702418755310 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273404837510621) ^ 757801612503540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273404837510621) ^ 454680967502124 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273404837510621) ^ 206673167046420 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273404837510621) ^ 63004873140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273404837510621) ^ 642999060 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2843694764652899 : Nat.Prime 2843694764652899 := by
  apply lucas_primality 2843694764652899 (2 : ZMod 2843694764652899)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (3203, 1), (161947, 1), (210853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (3203, 1), (161947, 1), (210853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843694764652899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_3203
      · exact prime_seventyFiveBU_161947
      · exact prime_seventyFiveBU_210853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2843694764652899) ^ 1421847382326449 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2843694764652899) ^ 218745751127146 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2843694764652899) ^ 887822280566 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2843694764652899) ^ 17559416134 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2843694764652899) ^ 13486622266 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2913683075424281 : Nat.Prime 2913683075424281 := by
  apply lucas_primality 2913683075424281 (3 : ZMod 2913683075424281)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (283, 1), (8101, 1), (31772929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (283, 1), (8101, 1), (31772929, 1)] : List FactorBlock).map factorBlockValue).prod) = 2913683075424281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_283
      · exact prime_seventyFiveBU_8101
      · exact prime_seventyFiveBU_31772929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2913683075424281) ^ 1456841537712140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2913683075424281) ^ 582736615084856 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2913683075424281) ^ 10295699913160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2913683075424281) ^ 359669556280 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2913683075424281) ^ 91703320 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5227726442036477 : Nat.Prime 5227726442036477 := by
  apply lucas_primality 5227726442036477 (2 : ZMod 5227726442036477)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (4341965483419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (4341965483419, 1)] : List FactorBlock).map factorBlockValue).prod) = 5227726442036477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_4341965483419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5227726442036477) ^ 2613863221018238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227726442036477) ^ 746818063148068 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227726442036477) ^ 121575033535732 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5227726442036477) ^ 1204 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5913970099176707 : Nat.Prime 5913970099176707 := by
  apply lucas_primality 5913970099176707 (5 : ZMod 5913970099176707)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (24848613862087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (24848613862087, 1)] : List FactorBlock).map factorBlockValue).prod) = 5913970099176707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_24848613862087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5913970099176707) ^ 2956985049588353 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5913970099176707) ^ 844852871310958 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5913970099176707) ^ 347880594069218 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5913970099176707) ^ 238 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_6855622793593361 : Nat.Prime 6855622793593361 := by
  apply lucas_primality 6855622793593361 (3 : ZMod 6855622793593361)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (85695284919917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (85695284919917, 1)] : List FactorBlock).map factorBlockValue).prod) = 6855622793593361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_85695284919917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6855622793593361) ^ 3427811396796680 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855622793593361) ^ 1371124558718672 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855622793593361) ^ 80 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_7387353436417291 : Nat.Prime 7387353436417291 := by
  apply lucas_primality 7387353436417291 (7 : ZMod 7387353436417291)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (23, 1), (8944285153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (23, 1), (8944285153, 1)] : List FactorBlock).map factorBlockValue).prod) = 7387353436417291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_8944285153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7387353436417291) ^ 3693676718208645 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 2462451145472430 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 1477470687283458 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 1055336205202470 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 388808075600910 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 321189279844230 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387353436417291) ^ 825930 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_8234442318267383 : Nat.Prime 8234442318267383 := by
  apply lucas_primality 8234442318267383 (5 : ZMod 8234442318267383)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (233, 1), (383, 1), (38098279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (233, 1), (383, 1), (38098279, 1)] : List FactorBlock).map factorBlockValue).prod) = 8234442318267383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_173
      · exact prime_seventyFiveBU_233
      · exact prime_seventyFiveBU_383
      · exact prime_seventyFiveBU_38098279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8234442318267383) ^ 4117221159133691 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8234442318267383) ^ 1176348902609626 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8234442318267383) ^ 47597932475534 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8234442318267383) ^ 35340954155654 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8234442318267383) ^ 21499849394954 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8234442318267383) ^ 216136858 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_10140599243648743 : Nat.Prime 10140599243648743 := by
  apply lucas_primality 10140599243648743 (3 : ZMod 10140599243648743)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2843, 1), (87557, 1), (617237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2843, 1), (87557, 1), (617237, 1)] : List FactorBlock).map factorBlockValue).prod) = 10140599243648743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_2843
      · exact prime_seventyFiveBU_87557
      · exact prime_seventyFiveBU_617237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10140599243648743) ^ 5070299621824371 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10140599243648743) ^ 3380199747882914 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10140599243648743) ^ 921872658513522 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10140599243648743) ^ 3566865720594 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10140599243648743) ^ 115817116206 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10140599243648743) ^ 16429020366 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_16380011865350801 : Nat.Prime 16380011865350801 := by
  apply lucas_primality 16380011865350801 (3 : ZMod 16380011865350801)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (40950029663377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (40950029663377, 1)] : List FactorBlock).map factorBlockValue).prod) = 16380011865350801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_40950029663377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16380011865350801) ^ 8190005932675400 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16380011865350801) ^ 3276002373070160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16380011865350801) ^ 400 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_19683420064233553 : Nat.Prime 19683420064233553 := by
  apply lucas_primality 19683420064233553 (5 : ZMod 19683420064233553)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (1380711283967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (1380711283967, 1)] : List FactorBlock).map factorBlockValue).prod) = 19683420064233553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_1380711283967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19683420064233553) ^ 9841710032116776 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 19683420064233553) ^ 6561140021411184 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 19683420064233553) ^ 1789401824021232 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 19683420064233553) ^ 14256 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_25001029170239027 : Nat.Prime 25001029170239027 := by
  apply lucas_primality 25001029170239027 (2 : ZMod 25001029170239027)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (181, 1), (2917, 1), (1029402103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (181, 1), (2917, 1), (1029402103, 1)] : List FactorBlock).map factorBlockValue).prod) = 25001029170239027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_181
      · exact prime_seventyFiveBU_2917
      · exact prime_seventyFiveBU_1029402103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25001029170239027) ^ 12500514585119513 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25001029170239027) ^ 1087001268271262 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25001029170239027) ^ 138127232984746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25001029170239027) ^ 8570801909578 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 25001029170239027) ^ 24286942 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_34482076082226527 : Nat.Prime 34482076082226527 := by
  apply lucas_primality 34482076082226527 (5 : ZMod 34482076082226527)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1326233695470251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1326233695470251, 1)] : List FactorBlock).map factorBlockValue).prod) = 34482076082226527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_1326233695470251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34482076082226527) ^ 17241038041113263 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 34482076082226527) ^ 2652467390940502 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 34482076082226527) ^ 26 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_42541758894320687 : Nat.Prime 42541758894320687 := by
  apply lucas_primality 42541758894320687 (5 : ZMod 42541758894320687)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (21249629817343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (21249629817343, 1)] : List FactorBlock).map factorBlockValue).prod) = 42541758894320687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_21249629817343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42541758894320687) ^ 21270879447160343 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 42541758894320687) ^ 6077394127760098 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 42541758894320687) ^ 3867432626756426 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 42541758894320687) ^ 3272442991870822 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 42541758894320687) ^ 2002 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_53368333654569737 : Nat.Prime 53368333654569737 := by
  apply lucas_primality 53368333654569737 (3 : ZMod 53368333654569737)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (606458336983747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (606458336983747, 1)] : List FactorBlock).map factorBlockValue).prod) = 53368333654569737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_606458336983747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53368333654569737) ^ 26684166827284868 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 53368333654569737) ^ 4851666695869976 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 53368333654569737) ^ 88 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_72342175732910609 : Nat.Prime 72342175732910609 := by
  apply lucas_primality 72342175732910609 (3 : ZMod 72342175732910609)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (179, 1), (3608448510221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (179, 1), (3608448510221, 1)] : List FactorBlock).map factorBlockValue).prod) = 72342175732910609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_179
      · exact prime_seventyFiveBU_3608448510221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72342175732910609) ^ 36171087866455304 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 72342175732910609) ^ 10334596533272944 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 72342175732910609) ^ 404146233144752 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 72342175732910609) ^ 20048 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_132367123368169289 : Nat.Prime 132367123368169289 := by
  apply lucas_primality 132367123368169289 (3 : ZMod 132367123368169289)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (943843, 1), (17530341827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (943843, 1), (17530341827, 1)] : List FactorBlock).map factorBlockValue).prod) = 132367123368169289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_943843
      · exact prime_seventyFiveBU_17530341827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 132367123368169289) ^ 66183561684084644 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132367123368169289) ^ 140242734616 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132367123368169289) ^ 7550744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_135835083081784459 : Nat.Prime 135835083081784459 := by
  apply lucas_primality 135835083081784459 (3 : ZMod 135835083081784459)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1999, 1), (83477, 1), (5024783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1999, 1), (83477, 1), (5024783, 1)] : List FactorBlock).map factorBlockValue).prod) = 135835083081784459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1999
      · exact prime_seventyFiveBU_83477
      · exact prime_seventyFiveBU_5024783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 135835083081784459) ^ 67917541540892229 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 135835083081784459) ^ 45278361027261486 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 135835083081784459) ^ 67951517299542 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 135835083081784459) ^ 1627215677154 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 135835083081784459) ^ 27033024726 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_137112455871867221 : Nat.Prime 137112455871867221 := by
  apply lucas_primality 137112455871867221 (2 : ZMod 137112455871867221)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6855622793593361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6855622793593361, 1)] : List FactorBlock).map factorBlockValue).prod) = 137112455871867221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_6855622793593361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 137112455871867221) ^ 68556227935933610 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 137112455871867221) ^ 27422491174373444 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 137112455871867221) ^ 20 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_154306142381591833 : Nat.Prime 154306142381591833 := by
  apply lucas_primality 154306142381591833 (5 : ZMod 154306142381591833)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (211, 1), (787, 1), (196538917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (211, 1), (787, 1), (196538917, 1)] : List FactorBlock).map factorBlockValue).prod) = 154306142381591833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_197
      · exact prime_seventyFiveBU_211
      · exact prime_seventyFiveBU_787
      · exact prime_seventyFiveBU_196538917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 154306142381591833) ^ 77153071190795916 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 154306142381591833) ^ 51435380793863944 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 154306142381591833) ^ 783279910566456 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 154306142381591833) ^ 731308731666312 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 154306142381591833) ^ 196068795910536 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 154306142381591833) ^ 785117496 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_215508123601198283 : Nat.Prime 215508123601198283 := by
  apply lucas_primality 215508123601198283 (2 : ZMod 215508123601198283)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (467627, 1), (5620179863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (467627, 1), (5620179863, 1)] : List FactorBlock).map factorBlockValue).prod) = 215508123601198283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_467627
      · exact prime_seventyFiveBU_5620179863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215508123601198283) ^ 107754061800599141 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 215508123601198283) ^ 5256295697590202 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 215508123601198283) ^ 460854748766 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 215508123601198283) ^ 38345414 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_255684568737270479 : Nat.Prime 255684568737270479 := by
  apply lucas_primality 255684568737270479 (7 : ZMod 255684568737270479)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (584387, 1), (16827927169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (584387, 1), (16827927169, 1)] : List FactorBlock).map factorBlockValue).prod) = 255684568737270479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_584387
      · exact prime_seventyFiveBU_16827927169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 255684568737270479) ^ 127842284368635239 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 255684568737270479) ^ 19668043749020806 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 255684568737270479) ^ 437526106394 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 255684568737270479) ^ 15194062 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_471411923026910297 : Nat.Prime 471411923026910297 := by
  apply lucas_primality 471411923026910297 (3 : ZMod 471411923026910297)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (261509, 1), (2187694681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (261509, 1), (2187694681, 1)] : List FactorBlock).map factorBlockValue).prod) = 471411923026910297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_103
      · exact prime_seventyFiveBU_261509
      · exact prime_seventyFiveBU_2187694681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 471411923026910297) ^ 235705961513455148 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471411923026910297) ^ 4576814786669032 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471411923026910297) ^ 1802660417144 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 471411923026910297) ^ 215483416 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_567436028990942227 : Nat.Prime 567436028990942227 := by
  apply lucas_primality 567436028990942227 (3 : ZMod 567436028990942227)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (2087, 1), (189603044747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (2087, 1), (189603044747, 1)] : List FactorBlock).map factorBlockValue).prod) = 567436028990942227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_239
      · exact prime_seventyFiveBU_2087
      · exact prime_seventyFiveBU_189603044747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 567436028990942227) ^ 283718014495471113 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 567436028990942227) ^ 189145342996980742 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 567436028990942227) ^ 2374209326321934 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 567436028990942227) ^ 271890766167198 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 567436028990942227) ^ 2992758 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_580073285494944533 : Nat.Prime 580073285494944533 := by
  apply lucas_primality 580073285494944533 (2 : ZMod 580073285494944533)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (132045437, 1), (1098245609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (132045437, 1), (1098245609, 1)] : List FactorBlock).map factorBlockValue).prod) = 580073285494944533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_132045437
      · exact prime_seventyFiveBU_1098245609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 580073285494944533) ^ 290036642747472266 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 580073285494944533) ^ 4392982436 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 580073285494944533) ^ 528181748 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1116511766274447359 : Nat.Prime 1116511766274447359 := by
  apply lucas_primality 1116511766274447359 (11 : ZMod 1116511766274447359)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3146359, 1), (177429175481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3146359, 1), (177429175481, 1)] : List FactorBlock).map factorBlockValue).prod) = 1116511766274447359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3146359
      · exact prime_seventyFiveBU_177429175481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1116511766274447359) ^ 558255883137223679 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1116511766274447359) ^ 354858350962 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1116511766274447359) ^ 6292718 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1616315646701174971 : Nat.Prime 1616315646701174971 := by
  apply lucas_primality 1616315646701174971 (2 : ZMod 1616315646701174971)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (32257, 1), (470059, 1), (3553273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (32257, 1), (470059, 1), (3553273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616315646701174971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_32257
      · exact prime_seventyFiveBU_470059
      · exact prime_seventyFiveBU_3553273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1616315646701174971) ^ 808157823350587485 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1616315646701174971) ^ 538771882233724990 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1616315646701174971) ^ 323263129340234994 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1616315646701174971) ^ 50107438593210 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1616315646701174971) ^ 3438537814830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1616315646701174971) ^ 454880794890 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3137188007938106557 : Nat.Prime 3137188007938106557 := by
  apply lucas_primality 3137188007938106557 (6 : ZMod 3137188007938106557)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (25703, 1), (151091, 1), (168719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (25703, 1), (151091, 1), (168719, 1)] : List FactorBlock).map factorBlockValue).prod) = 3137188007938106557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_25703
      · exact prime_seventyFiveBU_151091
      · exact prime_seventyFiveBU_168719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3137188007938106557) ^ 1568594003969053278 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 1045729335979368852 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 448169715419729508 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 165115158312531924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 122055324590052 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 20763566380116 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3137188007938106557) ^ 18594159566724 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3314061666542065249 : Nat.Prime 3314061666542065249 := by
  apply lucas_primality 3314061666542065249 (7 : ZMod 3314061666542065249)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (78901, 1), (145843000271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (78901, 1), (145843000271, 1)] : List FactorBlock).map factorBlockValue).prod) = 3314061666542065249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_78901
      · exact prime_seventyFiveBU_145843000271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3314061666542065249) ^ 1657030833271032624 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3314061666542065249) ^ 1104687222180688416 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3314061666542065249) ^ 42002784078048 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3314061666542065249) ^ 22723488 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3693368694463370437 : Nat.Prime 3693368694463370437 := by
  apply lucas_primality 3693368694463370437 (5 : ZMod 3693368694463370437)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (97, 1), (4757117181697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (97, 1), (4757117181697, 1)] : List FactorBlock).map factorBlockValue).prod) = 3693368694463370437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_29
      · exact prime_seventyFiveBU_97
      · exact prime_seventyFiveBU_4757117181697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3693368694463370437) ^ 1846684347231685218 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3693368694463370437) ^ 1231122898154456812 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3693368694463370437) ^ 160581247585363932 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3693368694463370437) ^ 127357541188392084 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3693368694463370437) ^ 38075965922302788 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3693368694463370437) ^ 776388 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3919487156506291547 : Nat.Prime 3919487156506291547 := by
  apply lucas_primality 3919487156506291547 (2 : ZMod 3919487156506291547)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (191, 1), (18126803, 1), (51457891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (191, 1), (18126803, 1), (51457891, 1)] : List FactorBlock).map factorBlockValue).prod) = 3919487156506291547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_191
      · exact prime_seventyFiveBU_18126803
      · exact prime_seventyFiveBU_51457891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3919487156506291547) ^ 1959743578253145773 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3919487156506291547) ^ 356317014227844686 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3919487156506291547) ^ 20520875164954406 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3919487156506291547) ^ 216226057982 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3919487156506291547) ^ 76168826206 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4571203579214341327 : Nat.Prime 4571203579214341327 := by
  apply lucas_primality 4571203579214341327 (3 : ZMod 4571203579214341327)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1277, 1), (25939439011351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1277, 1), (25939439011351, 1)] : List FactorBlock).map factorBlockValue).prod) = 4571203579214341327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_1277
      · exact prime_seventyFiveBU_25939439011351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4571203579214341327) ^ 2285601789607170663 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571203579214341327) ^ 1523734526404780442 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571203579214341327) ^ 198747981704971362 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571203579214341327) ^ 3579642583566438 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4571203579214341327) ^ 176226 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_12936754723249996757 : Nat.Prime 12936754723249996757 := by
  apply lucas_primality 12936754723249996757 (2 : ZMod 12936754723249996757)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (43308823, 1), (5744412511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (43308823, 1), (5744412511, 1)] : List FactorBlock).map factorBlockValue).prod) = 12936754723249996757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_43308823
      · exact prime_seventyFiveBU_5744412511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12936754723249996757) ^ 6468377361624998378 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12936754723249996757) ^ 995134978711538212 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12936754723249996757) ^ 298709450572 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12936754723249996757) ^ 2252058796 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_13867095319712464279 : Nat.Prime 13867095319712464279 := by
  apply lucas_primality 13867095319712464279 (6 : ZMod 13867095319712464279)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (687431, 1), (3362057505823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (687431, 1), (3362057505823, 1)] : List FactorBlock).map factorBlockValue).prod) = 13867095319712464279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_687431
      · exact prime_seventyFiveBU_3362057505823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 13867095319712464279) ^ 6933547659856232139 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13867095319712464279) ^ 4622365106570821426 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13867095319712464279) ^ 20172345034938 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13867095319712464279) ^ 4124586 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_15801541931519635903 : Nat.Prime 15801541931519635903 := by
  apply lucas_primality 15801541931519635903 (3 : ZMod 15801541931519635903)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (101, 1), (10315681, 1), (194439989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (101, 1), (10315681, 1), (194439989, 1)] : List FactorBlock).map factorBlockValue).prod) = 15801541931519635903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_101
      · exact prime_seventyFiveBU_10315681
      · exact prime_seventyFiveBU_194439989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15801541931519635903) ^ 7900770965759817951 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15801541931519635903) ^ 5267180643839878634 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15801541931519635903) ^ 1215503225501510454 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15801541931519635903) ^ 156450910213065702 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15801541931519635903) ^ 1531798233342 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15801541931519635903) ^ 81266934918 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_20774938776647807179 : Nat.Prime 20774938776647807179 := by
  apply lucas_primality 20774938776647807179 (3 : ZMod 20774938776647807179)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (149, 1), (30925243, 1), (35782429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (149, 1), (30925243, 1), (35782429, 1)] : List FactorBlock).map factorBlockValue).prod) = 20774938776647807179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_149
      · exact prime_seventyFiveBU_30925243
      · exact prime_seventyFiveBU_35782429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20774938776647807179) ^ 10387469388323903589 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20774938776647807179) ^ 6924979592215935726 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20774938776647807179) ^ 2967848396663972454 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20774938776647807179) ^ 139429119306361122 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20774938776647807179) ^ 671779322046 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20774938776647807179) ^ 580590512082 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_26774105155577191831 : Nat.Prime 26774105155577191831 := by
  apply lucas_primality 26774105155577191831 (3 : ZMod 26774105155577191831)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (17, 1), (83, 1), (613, 1), (1399, 1), (6095413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (17, 1), (83, 1), (613, 1), (1399, 1), (6095413, 1)] : List FactorBlock).map factorBlockValue).prod) = 26774105155577191831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_83
      · exact prime_seventyFiveBU_613
      · exact prime_seventyFiveBU_1399
      · exact prime_seventyFiveBU_6095413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26774105155577191831) ^ 13387052577788595915 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 8924701718525730610 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 5354821031115438366 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 2434009559597926530 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 1574947362092775990 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 322579580187677010 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 43677169911218910 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 19138030847446170 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26774105155577191831) ^ 4392500582910 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_46593712620201149021 : Nat.Prime 46593712620201149021 := by
  apply lucas_primality 46593712620201149021 (2 : ZMod 46593712620201149021)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (9923, 1), (896293, 1), (6091663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (9923, 1), (896293, 1), (6091663, 1)] : List FactorBlock).map factorBlockValue).prod) = 46593712620201149021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_43
      · exact prime_seventyFiveBU_9923
      · exact prime_seventyFiveBU_896293
      · exact prime_seventyFiveBU_6091663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46593712620201149021) ^ 23296856310100574510 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46593712620201149021) ^ 9318742524040229804 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46593712620201149021) ^ 1083574712097701140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46593712620201149021) ^ 4695526818522740 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46593712620201149021) ^ 51984911876140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 46593712620201149021) ^ 7648767277540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_65381140929877709213 : Nat.Prime 65381140929877709213 := by
  apply lucas_primality 65381140929877709213 (2 : ZMod 65381140929877709213)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (2521, 1), (209150045840353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (2521, 1), (209150045840353, 1)] : List FactorBlock).map factorBlockValue).prod) = 65381140929877709213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_31
      · exact prime_seventyFiveBU_2521
      · exact prime_seventyFiveBU_209150045840353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65381140929877709213) ^ 32690570464938854606 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 65381140929877709213) ^ 2109069062254119652 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 65381140929877709213) ^ 25934605684203772 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 65381140929877709213) ^ 312604 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_105099495954326415467 : Nat.Prime 105099495954326415467 := by
  apply lucas_primality 105099495954326415467 (2 : ZMod 105099495954326415467)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (132367123368169289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (132367123368169289, 1)] : List FactorBlock).map factorBlockValue).prod) = 105099495954326415467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_397
      · exact prime_seventyFiveBU_132367123368169289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105099495954326415467) ^ 52549747977163207733 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 105099495954326415467) ^ 264734246736338578 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 105099495954326415467) ^ 794 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_182737221779512247681 : Nat.Prime 182737221779512247681 := by
  apply lucas_primality 182737221779512247681 (3 : ZMod 182737221779512247681)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (23, 1), (67, 1), (509, 1), (112429, 1), (462541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (23, 1), (67, 1), (509, 1), (112429, 1), (462541, 1)] : List FactorBlock).map factorBlockValue).prod) = 182737221779512247681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_67
      · exact prime_seventyFiveBU_509
      · exact prime_seventyFiveBU_112429
      · exact prime_seventyFiveBU_462541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 182737221779512247681) ^ 91368610889756123840 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 36547444355902449536 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 26105317397073178240 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 7945096599109228160 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 2727421220589735040 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 359012223535387520 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 1625356640897920 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 182737221779512247681) ^ 395072483908480 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_188231280476286393421 : Nat.Prime 188231280476286393421 := by
  apply lucas_primality 188231280476286393421 (2 : ZMod 188231280476286393421)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3137188007938106557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3137188007938106557, 1)] : List FactorBlock).map factorBlockValue).prod) = 188231280476286393421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_3137188007938106557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188231280476286393421) ^ 94115640238143196710 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188231280476286393421) ^ 62743760158762131140 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188231280476286393421) ^ 37646256095257278684 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 188231280476286393421) ^ 60 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_316898149545705575417 : Nat.Prime 316898149545705575417 := by
  apply lucas_primality 316898149545705575417 (3 : ZMod 316898149545705575417)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (1201, 1), (36242267, 1), (39567947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (1201, 1), (36242267, 1), (39567947, 1)] : List FactorBlock).map factorBlockValue).prod) = 316898149545705575417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_1201
      · exact prime_seventyFiveBU_36242267
      · exact prime_seventyFiveBU_39567947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 316898149545705575417) ^ 158449074772852787708 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 316898149545705575417) ^ 13778180415030677192 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 316898149545705575417) ^ 263861906366116216 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 316898149545705575417) ^ 8743883199848 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 316898149545705575417) ^ 8008961130728 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_484610897705706814283 : Nat.Prime 484610897705706814283 := by
  apply lucas_primality 484610897705706814283 (2 : ZMod 484610897705706814283)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (112287419, 1), (2157903806239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (112287419, 1), (2157903806239, 1)] : List FactorBlock).map factorBlockValue).prod) = 484610897705706814283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_112287419
      · exact prime_seventyFiveBU_2157903806239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 484610897705706814283) ^ 242305448852853407141 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 484610897705706814283) ^ 4315807612478 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 484610897705706814283) ^ 224574838 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_827422644980449202449 : Nat.Prime 827422644980449202449 := by
  apply lucas_primality 827422644980449202449 (11 : ZMod 827422644980449202449)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (19, 1), (53368333654569737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (19, 1), (53368333654569737, 1)] : List FactorBlock).map factorBlockValue).prod) = 827422644980449202449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_53368333654569737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 827422644980449202449) ^ 413711322490224601224 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 827422644980449202449) ^ 275807548326816400816 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 827422644980449202449) ^ 48671920292967600144 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 827422644980449202449) ^ 43548560262128905392 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 827422644980449202449) ^ 15504 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_853414661458220384689 : Nat.Prime 853414661458220384689 := by
  apply lucas_primality 853414661458220384689 (7 : ZMod 853414661458220384689)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (1616315646701174971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (1616315646701174971, 1)] : List FactorBlock).map factorBlockValue).prod) = 853414661458220384689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_1616315646701174971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 853414661458220384689) ^ 426707330729110192344 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 853414661458220384689) ^ 284471553819406794896 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 853414661458220384689) ^ 77583151041656398608 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 853414661458220384689) ^ 528 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1758803244157542645533 : Nat.Prime 1758803244157542645533 := by
  apply lucas_primality 1758803244157542645533 (2 : ZMod 1758803244157542645533)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (109, 1), (211, 1), (313414062221797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (109, 1), (211, 1), (313414062221797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1758803244157542645533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_61
      · exact prime_seventyFiveBU_109
      · exact prime_seventyFiveBU_211
      · exact prime_seventyFiveBU_313414062221797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1758803244157542645533) ^ 879401622078771322766 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758803244157542645533) ^ 28832840068156436812 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758803244157542645533) ^ 16135809579426996748 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758803244157542645533) ^ 8335560398850913012 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758803244157542645533) ^ 5611756 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2643300779662145145457 : Nat.Prime 2643300779662145145457 := by
  apply lucas_primality 2643300779662145145457 (11 : ZMod 2643300779662145145457)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (44267, 1), (15358197113911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (44267, 1), (15358197113911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2643300779662145145457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_44267
      · exact prime_seventyFiveBU_15358197113911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2643300779662145145457) ^ 1321650389831072572728 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2643300779662145145457) ^ 881100259887381715152 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2643300779662145145457) ^ 59712670378885968 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 2643300779662145145457) ^ 172110096 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3043780077840419245301 : Nat.Prime 3043780077840419245301 := by
  apply lucas_primality 3043780077840419245301 (2 : ZMod 3043780077840419245301)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (2658793, 1), (1635425267803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (2658793, 1), (1635425267803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3043780077840419245301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_2658793
      · exact prime_seventyFiveBU_1635425267803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3043780077840419245301) ^ 1521890038920209622650 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043780077840419245301) ^ 608756015568083849060 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043780077840419245301) ^ 434825725405774177900 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043780077840419245301) ^ 1144797687462100 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043780077840419245301) ^ 1861155100 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3894061020399776257903 : Nat.Prime 3894061020399776257903 := by
  apply lucas_primality 3894061020399776257903 (3 : ZMod 3894061020399776257903)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (587, 1), (4649, 1), (58099, 1), (104959219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (587, 1), (4649, 1), (58099, 1), (104959219, 1)] : List FactorBlock).map factorBlockValue).prod) = 3894061020399776257903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_587
      · exact prime_seventyFiveBU_4649
      · exact prime_seventyFiveBU_58099
      · exact prime_seventyFiveBU_104959219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3894061020399776257903) ^ 1947030510199888128951 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 1298020340133258752634 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 299543155415367404454 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 6633834787733860746 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 837612609249252798 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 67024579087415898 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3894061020399776257903) ^ 37100704992858 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4932726529330562658569 : Nat.Prime 4932726529330562658569 := by
  apply lucas_primality 4932726529330562658569 (3 : ZMod 4932726529330562658569)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (280843, 1), (2195500034418947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (280843, 1), (2195500034418947, 1)] : List FactorBlock).map factorBlockValue).prod) = 4932726529330562658569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_280843
      · exact prime_seventyFiveBU_2195500034418947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4932726529330562658569) ^ 2466363264665281329284 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4932726529330562658569) ^ 17564000275351576 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4932726529330562658569) ^ 2246744 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_14466017151976955536681 : Nat.Prime 14466017151976955536681 := by
  apply lucas_primality 14466017151976955536681 (7 : ZMod 14466017151976955536681)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (179, 1), (37813, 1), (937389237703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (179, 1), (37813, 1), (937389237703, 1)] : List FactorBlock).map factorBlockValue).prod) = 14466017151976955536681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_179
      · exact prime_seventyFiveBU_37813
      · exact prime_seventyFiveBU_937389237703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14466017151976955536681) ^ 7233008575988477768340 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 4822005717325651845560 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 2893203430395391107336 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 761369323788260817720 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 80815738279200868920 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 382567295691348360 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 14466017151976955536681) ^ 15432241560 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_45159576867886579079081 : Nat.Prime 45159576867886579079081 := by
  apply lucas_primality 45159576867886579079081 (6 : ZMod 45159576867886579079081)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (31, 1), (5265961, 1), (628720839077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (31, 1), (5265961, 1), (628720839077, 1)] : List FactorBlock).map factorBlockValue).prod) = 45159576867886579079081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_11
      · exact prime_seventyFiveBU_31
      · exact prime_seventyFiveBU_5265961
      · exact prime_seventyFiveBU_628720839077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45159576867886579079081) ^ 22579788433943289539540 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 45159576867886579079081) ^ 9031915373577315815816 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 45159576867886579079081) ^ 4105416078898779916280 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 45159576867886579079081) ^ 1456760544125373518680 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 45159576867886579079081) ^ 8575752245010280 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 45159576867886579079081) ^ 71827708040 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_85518076559941897545517 : Nat.Prime 85518076559941897545517 := by
  apply lucas_primality 85518076559941897545517 (5 : ZMod 85518076559941897545517)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1559, 1), (4571203579214341327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1559, 1), (4571203579214341327, 1)] : List FactorBlock).map factorBlockValue).prod) = 85518076559941897545517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_1559
      · exact prime_seventyFiveBU_4571203579214341327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 85518076559941897545517) ^ 42759038279970948772758 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 85518076559941897545517) ^ 28506025519980632515172 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 85518076559941897545517) ^ 54854442950572095924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 85518076559941897545517) ^ 18708 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_105046192485190439653067 : Nat.Prime 105046192485190439653067 := by
  apply lucas_primality 105046192485190439653067 (2 : ZMod 105046192485190439653067)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (55849, 1), (72342175732910609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (55849, 1), (72342175732910609, 1)] : List FactorBlock).map factorBlockValue).prod) = 105046192485190439653067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_13
      · exact prime_seventyFiveBU_55849
      · exact prime_seventyFiveBU_72342175732910609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105046192485190439653067) ^ 52523096242595219826533 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 105046192485190439653067) ^ 8080476345014649204082 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 105046192485190439653067) ^ 1880896569055675834 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 105046192485190439653067) ^ 1452074 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_151157446651184994490949 : Nat.Prime 151157446651184994490949 := by
  apply lucas_primality 151157446651184994490949 (2 : ZMod 151157446651184994490949)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2449999, 1), (3390953, 1), (4548643271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2449999, 1), (3390953, 1), (4548643271, 1)] : List FactorBlock).map factorBlockValue).prod) = 151157446651184994490949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_2449999
      · exact prime_seventyFiveBU_3390953
      · exact prime_seventyFiveBU_4548643271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151157446651184994490949) ^ 75578723325592497245474 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 151157446651184994490949) ^ 61696942182909052 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 151157446651184994490949) ^ 44576685861226916 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 151157446651184994490949) ^ 33231325836188 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1008209581886019876101243 : Nat.Prime 1008209581886019876101243 := by
  apply lucas_primality 1008209581886019876101243 (5 : ZMod 1008209581886019876101243)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (856139, 1), (2273404837510621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (856139, 1), (2273404837510621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008209581886019876101243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_37
      · exact prime_seventyFiveBU_856139
      · exact prime_seventyFiveBU_2273404837510621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1008209581886019876101243) ^ 504104790943009938050621 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008209581886019876101243) ^ 144029940269431410871606 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008209581886019876101243) ^ 27248907618541077732466 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008209581886019876101243) ^ 1177623705830501678 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1008209581886019876101243) ^ 443480002 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1182613784146171891266133 : Nat.Prime 1182613784146171891266133 := by
  apply lucas_primality 1182613784146171891266133 (2 : ZMod 1182613784146171891266133)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (79, 1), (849581, 1), (163150082827621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (79, 1), (849581, 1), (163150082827621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182613784146171891266133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_79
      · exact prime_seventyFiveBU_849581
      · exact prime_seventyFiveBU_163150082827621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1182613784146171891266133) ^ 591306892073085945633066 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182613784146171891266133) ^ 394204594715390630422044 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182613784146171891266133) ^ 14969794736027492294508 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182613784146171891266133) ^ 1391996506685262372 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182613784146171891266133) ^ 7248625092 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1668580122837576938020589 : Nat.Prime 1668580122837576938020589 := by
  apply lucas_primality 1668580122837576938020589 (2 : ZMod 1668580122837576938020589)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (311, 1), (32242169, 1), (240467468921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (311, 1), (32242169, 1), (240467468921, 1)] : List FactorBlock).map factorBlockValue).prod) = 1668580122837576938020589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_173
      · exact prime_seventyFiveBU_311
      · exact prime_seventyFiveBU_32242169
      · exact prime_seventyFiveBU_240467468921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1668580122837576938020589) ^ 834290061418788469010294 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668580122837576938020589) ^ 9644971808309693283356 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668580122837576938020589) ^ 5365209398191565717108 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668580122837576938020589) ^ 51751484921426252 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1668580122837576938020589) ^ 6938901674828 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_2575744845539917968434339 : Nat.Prime 2575744845539917968434339 := by
  apply lucas_primality 2575744845539917968434339 (2 : ZMod 2575744845539917968434339)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (57327013, 1), (59275376359847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (57327013, 1), (59275376359847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2575744845539917968434339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_379
      · exact prime_seventyFiveBU_57327013
      · exact prime_seventyFiveBU_59275376359847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2575744845539917968434339) ^ 1287872422769958984217169 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2575744845539917968434339) ^ 6796160542321683294022 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2575744845539917968434339) ^ 44930735280764026 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2575744845539917968434339) ^ 43453875854 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_3342506646098902143522019 : Nat.Prime 3342506646098902143522019 := by
  apply lucas_primality 3342506646098902143522019 (2 : ZMod 3342506646098902143522019)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (947, 1), (31151, 1), (1110836485880647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (947, 1), (31151, 1), (1110836485880647, 1)] : List FactorBlock).map factorBlockValue).prod) = 3342506646098902143522019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_17
      · exact prime_seventyFiveBU_947
      · exact prime_seventyFiveBU_31151
      · exact prime_seventyFiveBU_1110836485880647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3342506646098902143522019) ^ 1671253323049451071761009 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3342506646098902143522019) ^ 1114168882032967381174006 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3342506646098902143522019) ^ 196618038005817773148354 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3342506646098902143522019) ^ 3529574071910139539094 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3342506646098902143522019) ^ 107300139517155216318 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3342506646098902143522019) ^ 3008999694 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_4155692754731765293309843 : Nat.Prime 4155692754731765293309843 := by
  apply lucas_primality 4155692754731765293309843 (2 : ZMod 4155692754731765293309843)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (197, 1), (643, 1), (58169, 1), (1326041, 1), (23628991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (197, 1), (643, 1), (58169, 1), (1326041, 1), (23628991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4155692754731765293309843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_197
      · exact prime_seventyFiveBU_643
      · exact prime_seventyFiveBU_58169
      · exact prime_seventyFiveBU_1326041
      · exact prime_seventyFiveBU_23628991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4155692754731765293309843) ^ 2077846377365882646654921 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 1385230918243921764436614 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 21094887079856676615786 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 6462974735197146645894 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 71441708723405341218 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 3133909701684763362 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4155692754731765293309843) ^ 175872628447476462 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5001128951365576766122511 : Nat.Prime 5001128951365576766122511 := by
  apply lucas_primality 5001128951365576766122511 (11 : ZMod 5001128951365576766122511)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1060883, 1), (471411923026910297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1060883, 1), (471411923026910297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5001128951365576766122511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_1060883
      · exact prime_seventyFiveBU_471411923026910297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5001128951365576766122511) ^ 2500564475682788383061255 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5001128951365576766122511) ^ 1000225790273115353224502 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5001128951365576766122511) ^ 4714119230269102970 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5001128951365576766122511) ^ 10608830 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_12942638491856907905904557 : Nat.Prime 12942638491856907905904557 := by
  apply lucas_primality 12942638491856907905904557 (2 : ZMod 12942638491856907905904557)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (396708707, 1), (429276877184483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (396708707, 1), (429276877184483, 1)] : List FactorBlock).map factorBlockValue).prod) = 12942638491856907905904557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_19
      · exact prime_seventyFiveBU_396708707
      · exact prime_seventyFiveBU_429276877184483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12942638491856907905904557) ^ 6471319245928453952952278 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942638491856907905904557) ^ 681191499571416205573924 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942638491856907905904557) ^ 32625042666020708 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942638491856907905904557) ^ 30149861732 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_29062607770472525750033471 : Nat.Prime 29062607770472525750033471 := by
  apply lucas_primality 29062607770472525750033471 (7 : ZMod 29062607770472525750033471)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (36473, 1), (2359789, 1), (689118392999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (36473, 1), (2359789, 1), (689118392999, 1)] : List FactorBlock).map factorBlockValue).prod) = 29062607770472525750033471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_36473
      · exact prime_seventyFiveBU_2359789
      · exact prime_seventyFiveBU_689118392999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29062607770472525750033471) ^ 14531303885236262875016735 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 29062607770472525750033471) ^ 5812521554094505150006694 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 29062607770472525750033471) ^ 4151801110067503678576210 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 29062607770472525750033471) ^ 796825261713391433390 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 29062607770472525750033471) ^ 12315765422447738230 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (7 : ZMod 29062607770472525750033471) ^ 42173606256530 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_62886536388447997208051149 : Nat.Prime 62886536388447997208051149 := by
  apply lucas_primality 62886536388447997208051149 (2 : ZMod 62886536388447997208051149)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (719, 1), (316898149545705575417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (719, 1), (316898149545705575417, 1)] : List FactorBlock).map factorBlockValue).prod) = 62886536388447997208051149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_23
      · exact prime_seventyFiveBU_719
      · exact prime_seventyFiveBU_316898149545705575417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62886536388447997208051149) ^ 31443268194223998604025574 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 62886536388447997208051149) ^ 20962178796149332402683716 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 62886536388447997208051149) ^ 2734197234280347704697876 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 62886536388447997208051149) ^ 87463889274614738815092 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 62886536388447997208051149) ^ 198444 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_127034407317638504388756619 : Nat.Prime 127034407317638504388756619 := by
  apply lucas_primality 127034407317638504388756619 (3 : ZMod 127034407317638504388756619)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1008209581886019876101243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1008209581886019876101243, 1)] : List FactorBlock).map factorBlockValue).prod) = 127034407317638504388756619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_1008209581886019876101243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 127034407317638504388756619) ^ 63517203658819252194378309 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127034407317638504388756619) ^ 42344802439212834796252206 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127034407317638504388756619) ^ 18147772473948357769822374 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 127034407317638504388756619) ^ 126 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_132938555183975526331862249 : Nat.Prime 132938555183975526331862249 := by
  apply lucas_primality 132938555183975526331862249 (3 : ZMod 132938555183975526331862249)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (509, 1), (2003, 1), (54727, 1), (297824618375789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (509, 1), (2003, 1), (54727, 1), (297824618375789, 1)] : List FactorBlock).map factorBlockValue).prod) = 132938555183975526331862249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_509
      · exact prime_seventyFiveBU_2003
      · exact prime_seventyFiveBU_54727
      · exact prime_seventyFiveBU_297824618375789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132938555183975526331862249) ^ 66469277591987763165931124 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132938555183975526331862249) ^ 261175943386985316958472 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132938555183975526331862249) ^ 66369723007476548343416 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132938555183975526331862249) ^ 2429121917590504254424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (3 : ZMod 132938555183975526331862249) ^ 446365233032 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_157495588468404397981087247 : Nat.Prime 157495588468404397981087247 := by
  apply lucas_primality 157495588468404397981087247 (5 : ZMod 157495588468404397981087247)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (3109, 1), (105099495954326415467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (3109, 1), (105099495954326415467, 1)] : List FactorBlock).map factorBlockValue).prod) = 157495588468404397981087247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_241
      · exact prime_seventyFiveBU_3109
      · exact prime_seventyFiveBU_105099495954326415467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 157495588468404397981087247) ^ 78747794234202198990543623 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 157495588468404397981087247) ^ 653508665844001651373806 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 157495588468404397981087247) ^ 50657957049985332255094 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 157495588468404397981087247) ^ 1498538 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_161218211468566683751549309 : Nat.Prime 161218211468566683751549309 := by
  apply lucas_primality 161218211468566683751549309 (6 : ZMod 161218211468566683751549309)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (41, 1), (937, 1), (101212019, 1), (383914758287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (41, 1), (937, 1), (101212019, 1), (383914758287, 1)] : List FactorBlock).map factorBlockValue).prod) = 161218211468566683751549309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_41
      · exact prime_seventyFiveBU_937
      · exact prime_seventyFiveBU_101212019
      · exact prime_seventyFiveBU_383914758287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 161218211468566683751549309) ^ 80609105734283341875774654 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 161218211468566683751549309) ^ 53739403822855561250516436 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 161218211468566683751549309) ^ 3932151499233333750037788 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 161218211468566683751549309) ^ 172057856423230185433884 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 161218211468566683751549309) ^ 1592876153064061332 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 161218211468566683751549309) ^ 419932310463684 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1055595432234662810278001429 : Nat.Prime 1055595432234662810278001429 := by
  apply lucas_primality 1055595432234662810278001429 (2 : ZMod 1055595432234662810278001429)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2441, 1), (2344345193, 1), (46115632735189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2441, 1), (2344345193, 1), (46115632735189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1055595432234662810278001429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_2441
      · exact prime_seventyFiveBU_2344345193
      · exact prime_seventyFiveBU_46115632735189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1055595432234662810278001429) ^ 527797716117331405139000714 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1055595432234662810278001429) ^ 432443847699575096385908 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1055595432234662810278001429) ^ 450273038026385396 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1055595432234662810278001429) ^ 22890186464452 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1453606824716584853497575739 : Nat.Prime 1453606824716584853497575739 := by
  apply lucas_primality 1453606824716584853497575739 (10 : ZMod 1453606824716584853497575739)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (50821, 1), (5397163, 1), (18160367, 1), (48636503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (50821, 1), (5397163, 1), (18160367, 1), (48636503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1453606824716584853497575739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_50821
      · exact prime_seventyFiveBU_5397163
      · exact prime_seventyFiveBU_18160367
      · exact prime_seventyFiveBU_48636503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1453606824716584853497575739) ^ 726803412358292426748787869 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1453606824716584853497575739) ^ 484535608238861617832525246 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1453606824716584853497575739) ^ 28602483711784200497778 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1453606824716584853497575739) ^ 269327945944301636526 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1453606824716584853497575739) ^ 80042811068553011814 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 1453606824716584853497575739) ^ 29887157485738332246 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_1612182114685666837515493091 : Nat.Prime 1612182114685666837515493091 := by
  apply lucas_primality 1612182114685666837515493091 (6 : ZMod 1612182114685666837515493091)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (161218211468566683751549309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (161218211468566683751549309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1612182114685666837515493091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_161218211468566683751549309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1612182114685666837515493091) ^ 806091057342833418757746545 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1612182114685666837515493091) ^ 322436422937133367503098618 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 1612182114685666837515493091) ^ 10 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_5215883312218333886079536473 : Nat.Prime 5215883312218333886079536473 := by
  apply lucas_primality 5215883312218333886079536473 (11 : ZMod 5215883312218333886079536473)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11041194601, 1), (19683420064233553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11041194601, 1), (19683420064233553, 1)] : List FactorBlock).map factorBlockValue).prod) = 5215883312218333886079536473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_11041194601
      · exact prime_seventyFiveBU_19683420064233553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5215883312218333886079536473) ^ 2607941656109166943039768236 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5215883312218333886079536473) ^ 1738627770739444628693178824 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5215883312218333886079536473) ^ 472402081541605272 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 5215883312218333886079536473) ^ 264988670424 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_6333572593407976861668008573 : Nat.Prime 6333572593407976861668008573 := by
  apply lucas_primality 6333572593407976861668008573 (2 : ZMod 6333572593407976861668008573)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (397, 1), (11317, 1), (88085341, 1), (571564515661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (397, 1), (11317, 1), (88085341, 1), (571564515661, 1)] : List FactorBlock).map factorBlockValue).prod) = 6333572593407976861668008573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_397
      · exact prime_seventyFiveBU_11317
      · exact prime_seventyFiveBU_88085341
      · exact prime_seventyFiveBU_571564515661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6333572593407976861668008573) ^ 3166786296703988430834004286 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6333572593407976861668008573) ^ 904796084772568123095429796 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6333572593407976861668008573) ^ 15953583358710269172967276 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6333572593407976861668008573) ^ 559651196731287166357516 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6333572593407976861668008573) ^ 71902685753444229292 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6333572593407976861668008573) ^ 11081115814342252 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_9852224034190186229261346671 : Nat.Prime 9852224034190186229261346671 := by
  apply lucas_primality 9852224034190186229261346671 (11 : ZMod 9852224034190186229261346671)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (197, 1), (5001128951365576766122511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (197, 1), (5001128951365576766122511, 1)] : List FactorBlock).map factorBlockValue).prod) = 9852224034190186229261346671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_197
      · exact prime_seventyFiveBU_5001128951365576766122511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9852224034190186229261346671) ^ 4926112017095093114630673335 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 9852224034190186229261346671) ^ 1970444806838037245852269334 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 9852224034190186229261346671) ^ 50011289513655767661225110 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (11 : ZMod 9852224034190186229261346671) ^ 1970 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_17734003261542335212670424019 : Nat.Prime 17734003261542335212670424019 := by
  apply lucas_primality 17734003261542335212670424019 (2 : ZMod 17734003261542335212670424019)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (62886536388447997208051149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (62886536388447997208051149, 1)] : List FactorBlock).map factorBlockValue).prod) = 17734003261542335212670424019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_47
      · exact prime_seventyFiveBU_62886536388447997208051149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17734003261542335212670424019) ^ 8867001630771167606335212009 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17734003261542335212670424019) ^ 5911334420514111737556808006 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17734003261542335212670424019) ^ 377319218330687983248306894 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17734003261542335212670424019) ^ 282 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_44335008153855838031676060043 : Nat.Prime 44335008153855838031676060043 := by
  apply lucas_primality 44335008153855838031676060043 (2 : ZMod 44335008153855838031676060043)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2976781, 1), (827422644980449202449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2976781, 1), (827422644980449202449, 1)] : List FactorBlock).map factorBlockValue).prod) = 44335008153855838031676060043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_2976781
      · exact prime_seventyFiveBU_827422644980449202449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44335008153855838031676060043) ^ 22167504076927919015838030021 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44335008153855838031676060043) ^ 14778336051285279343892020014 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44335008153855838031676060043) ^ 14893607609648085644082 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44335008153855838031676060043) ^ 53582058 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_88670016307711676063352120013 : Nat.Prime 88670016307711676063352120013 := by
  apply lucas_primality 88670016307711676063352120013 (6 : ZMod 88670016307711676063352120013)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (181, 1), (12457, 1), (208963, 1), (5227726442036477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (181, 1), (12457, 1), (208963, 1), (5227726442036477, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_3
      · exact prime_seventyFiveBU_181
      · exact prime_seventyFiveBU_12457
      · exact prime_seventyFiveBU_208963
      · exact prime_seventyFiveBU_5227726442036477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 88670016307711676063352120013) ^ 44335008153855838031676060006 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711676063352120013) ^ 29556672102570558687784040004 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711676063352120013) ^ 489889592860285503112442652 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711676063352120013) ^ 7118087525705360525275116 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711676063352120013) ^ 424333572487529735232324 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88670016307711676063352120013) ^ 16961487424956 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_88670016307711676063352120023 : Nat.Prime 88670016307711676063352120023 := by
  apply lucas_primality 88670016307711676063352120023 (5 : ZMod 88670016307711676063352120023)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6333572593407976861668008573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6333572593407976861668008573, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_7
      · exact prime_seventyFiveBU_6333572593407976861668008573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 88670016307711676063352120023) ^ 44335008153855838031676060011 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 88670016307711676063352120023) ^ 12667145186815953723336017146 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (5 : ZMod 88670016307711676063352120023) ^ 14 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem prime_seventyFiveBU_88670016307711676063352120101 : Nat.Prime 88670016307711676063352120101 := by
  apply lucas_primality 88670016307711676063352120101 (10 : ZMod 88670016307711676063352120101)
  · rw [← seventyFiveBUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (199, 1), (38917, 1), (3693368694463370437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (199, 1), (38917, 1), (3693368694463370437, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventyFiveBU_2
      · exact prime_seventyFiveBU_5
      · exact prime_seventyFiveBU_31
      · exact prime_seventyFiveBU_199
      · exact prime_seventyFiveBU_38917
      · exact prime_seventyFiveBU_3693368694463370437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 88670016307711676063352120101) ^ 44335008153855838031676060050 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88670016307711676063352120101) ^ 17734003261542335212670424020 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88670016307711676063352120101) ^ 2860323106700376647204907100 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88670016307711676063352120101) ^ 445577971395536060619859900 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88670016307711676063352120101) ^ 2278439147614453222585300 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88670016307711676063352120101) ^ 24007897300 ≠ 1
      rw [← seventyFiveBUFastPow_eq_pow]
      decide

private theorem phi_seventyFiveBU_88670016307711676063352120000 : Nat.totient 88670016307711676063352120000 = 23622961683280677577359360000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 4), (1061, 1), (264977, 1), (40096957, 1), (65548169, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_1061, prime_seventyFiveBU_264977, prime_seventyFiveBU_40096957, prime_seventyFiveBU_65548169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120001 : Nat.totient 88670016307711676063352120001 = 76000120880439454123008052224 := by
  rw [← show ((([(7, 1), (38119, 1), (100853, 1), (26879933, 1), (122580177553, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_7, prime_seventyFiveBU_38119, prime_seventyFiveBU_100853, prime_seventyFiveBU_26879933, prime_seventyFiveBU_122580177553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120002 : Nat.totient 88670016307711676063352120002 = 43927979483299562611436245248 := by
  rw [← show ((([(2, 1), (109, 1), (153877, 1), (2643300779662145145457, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_109, prime_seventyFiveBU_153877, prime_seventyFiveBU_2643300779662145145457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120003 : Nat.totient 88670016307711676063352120003 = 57706333649747836199024256000 := by
  rw [← show ((([(3, 2), (43, 1), (1789, 1), (7818821, 1), (16380011865350801, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_43, prime_seventyFiveBU_1789, prime_seventyFiveBU_7818821, prime_seventyFiveBU_16380011865350801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120004 : Nat.totient 88670016307711676063352120004 = 44289840828387692525700257280 := by
  rw [← show ((([(2, 2), (1231, 1), (5009, 1), (143797, 1), (25001029170239027, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_1231, prime_seventyFiveBU_5009, prime_seventyFiveBU_143797, prime_seventyFiveBU_25001029170239027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120005 : Nat.totient 88670016307711676063352120005 = 64487284587426673500619723600 := by
  rw [← show ((([(5, 1), (11, 1), (1612182114685666837515493091, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_11, prime_seventyFiveBU_1612182114685666837515493091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120006 : Nat.totient 88670016307711676063352120006 = 29556672102296333560475119200 := by
  rw [← show ((([(2, 1), (3, 1), (107782593181, 1), (137112455871867221, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_107782593181, prime_seventyFiveBU_137112455871867221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120007 : Nat.totient 88670016307711676063352120007 = 74549597713095789538010242560 := by
  rw [← show ((([(13, 1), (17, 1), (31, 1), (12942638491856907905904557, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_13, prime_seventyFiveBU_17, prime_seventyFiveBU_31, prime_seventyFiveBU_12942638491856907905904557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120008 : Nat.totient 88670016307711676063352120008 = 37902364180961984062819891200 := by
  rw [← show ((([(2, 3), (7, 2), (397, 1), (11317, 1), (88085341, 1), (571564515661, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_7, prime_seventyFiveBU_397, prime_seventyFiveBU_11317, prime_seventyFiveBU_88085341, prime_seventyFiveBU_571564515661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120009 : Nat.totient 88670016307711676063352120009 = 59105520944694524801392312320 := by
  rw [← show ((([(3, 1), (7621, 1), (1420369, 1), (2363393, 1), (1155331041079, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_7621, prime_seventyFiveBU_1420369, prime_seventyFiveBU_2363393, prime_seventyFiveBU_1155331041079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120010 : Nat.totient 88670016307711676063352120010 = 34797699943905379498035213312 := by
  rw [← show ((([(2, 1), (5, 1), (53, 1), (31667, 1), (3151525759, 1), (1676382565489, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_53, prime_seventyFiveBU_31667, prime_seventyFiveBU_3151525759, prime_seventyFiveBU_1676382565489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120011 : Nat.totient 88670016307711676063352120011 = 88418826412000525952159311872 := by
  rw [← show ((([(353, 1), (1849226593, 1), (135835083081784459, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_353, prime_seventyFiveBU_1849226593, prime_seventyFiveBU_135835083081784459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120012 : Nat.totient 88670016307711676063352120012 = 29390875332821214931278443520 := by
  rw [← show ((([(2, 2), (3, 2), (181, 1), (12457, 1), (208963, 1), (5227726442036477, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_181, prime_seventyFiveBU_12457, prime_seventyFiveBU_208963, prime_seventyFiveBU_5227726442036477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120013 : Nat.totient 88670016307711676063352120013 = 88670016307711676063352120012 := by
  rw [← show ((([(88670016307711676063352120013, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_88670016307711676063352120013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120014 : Nat.totient 88670016307711676063352120014 = 42406316072326836476284838400 := by
  rw [← show ((([(2, 1), (23, 1), (39191, 1), (44103361, 1), (1115220963141559, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_23, prime_seventyFiveBU_39191, prime_seventyFiveBU_44103361, prime_seventyFiveBU_1115220963141559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120015 : Nat.totient 88670016307711676063352120015 = 37078594562729171969814528000 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (19, 1), (41, 1), (97, 1), (71216717071, 1), (156926521291, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_7, prime_seventyFiveBU_19, prime_seventyFiveBU_41, prime_seventyFiveBU_97, prime_seventyFiveBU_71216717071, prime_seventyFiveBU_156926521291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120016 : Nat.totient 88670016307711676063352120016 = 40255620771366437664730406400 := by
  rw [← show ((([(2, 4), (11, 1), (827, 1), (205211, 1), (636227069, 1), (4666011787, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_11, prime_seventyFiveBU_827, prime_seventyFiveBU_205211, prime_seventyFiveBU_636227069, prime_seventyFiveBU_4666011787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120017 : Nat.totient 88670016307711676063352120017 = 88020230600251862507103022800 := by
  rw [← show ((([(179, 1), (571, 1), (85550791, 1), (10140599243648743, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_179, prime_seventyFiveBU_571, prime_seventyFiveBU_85550791, prime_seventyFiveBU_10140599243648743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120018 : Nat.totient 88670016307711676063352120018 = 29071556859648864122889465600 := by
  rw [← show ((([(2, 1), (3, 1), (61, 1), (50821, 1), (5397163, 1), (18160367, 1), (48636503, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_61, prime_seventyFiveBU_50821, prime_seventyFiveBU_5397163, prime_seventyFiveBU_18160367, prime_seventyFiveBU_48636503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120019 : Nat.totient 88670016307711676063352120019 = 88156767080609224283236642560 := by
  rw [← show ((([(173, 1), (125299, 1), (40009261, 1), (102240402499577, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_173, prime_seventyFiveBU_125299, prime_seventyFiveBU_40009261, prime_seventyFiveBU_102240402499577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120020 : Nat.totient 88670016307711676063352120020 = 32705073633934797560272000512 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (947, 1), (620827, 1), (580073285494944533, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_13, prime_seventyFiveBU_947, prime_seventyFiveBU_620827, prime_seventyFiveBU_580073285494944533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120021 : Nat.totient 88670016307711676063352120021 = 58590217265272611912067475520 := by
  rw [← show ((([(3, 3), (113, 1), (29062607770472525750033471, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_113, prime_seventyFiveBU_29062607770472525750033471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120022 : Nat.totient 88670016307711676063352120022 = 38001435560447861170008051432 := by
  rw [← show ((([(2, 1), (7, 1), (6333572593407976861668008573, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_7, prime_seventyFiveBU_6333572593407976861668008573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120023 : Nat.totient 88670016307711676063352120023 = 88670016307711676063352120022 := by
  rw [← show ((([(88670016307711676063352120023, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_88670016307711676063352120023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120024 : Nat.totient 88670016307711676063352120024 = 27818044329311634877596057600 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (11041194601, 1), (19683420064233553, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_17, prime_seventyFiveBU_11041194601, prime_seventyFiveBU_19683420064233553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120025 : Nat.totient 88670016307711676063352120025 = 68486983508255873339415490560 := by
  rw [← show ((([(5, 2), (29, 1), (23173, 1), (15118249, 1), (349104161751497, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_29, prime_seventyFiveBU_23173, prime_seventyFiveBU_15118249, prime_seventyFiveBU_349104161751497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120026 : Nat.totient 88670016307711676063352120026 = 44335007965624557555154131840 := by
  rw [← show ((([(2, 1), (235534753, 1), (188231280476286393421, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_235534753, prime_seventyFiveBU_188231280476286393421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120027 : Nat.totient 88670016307711676063352120027 = 53216673431936323538112122400 := by
  rw [← show ((([(3, 1), (11, 1), (103, 1), (53831, 1), (484610897705706814283, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_11, prime_seventyFiveBU_103, prime_seventyFiveBU_53831, prime_seventyFiveBU_484610897705706814283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120028 : Nat.totient 88670016307711676063352120028 = 43917258074264013104543324160 := by
  rw [← show ((([(2, 2), (127, 1), (641, 1), (1263547, 1), (215508123601198283, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_127, prime_seventyFiveBU_641, prime_seventyFiveBU_1263547, prime_seventyFiveBU_215508123601198283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120029 : Nat.totient 88670016307711676063352120029 = 75981613644533720972231692992 := by
  rw [← show ((([(7, 1), (3643, 1), (198943, 1), (5920939, 1), (2951891072477, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_7, prime_seventyFiveBU_3643, prime_seventyFiveBU_198943, prime_seventyFiveBU_5920939, prime_seventyFiveBU_2951891072477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120030 : Nat.totient 88670016307711676063352120030 = 23525310587223673107840287040 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (197, 1), (5001128951365576766122511, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_197, prime_seventyFiveBU_5001128951365576766122511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120031 : Nat.totient 88670016307711676063352120031 = 86268342491197052856939517248 := by
  rw [← show ((([(37, 2), (16633, 1), (3894061020399776257903, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_37, prime_seventyFiveBU_16633, prime_seventyFiveBU_3894061020399776257903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120032 : Nat.totient 88670016307711676063352120032 = 44281528047518255597379694464 := by
  rw [← show ((([(2, 5), (829, 1), (3342506646098902143522019, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_829, prime_seventyFiveBU_3342506646098902143522019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120033 : Nat.totient 88670016307711676063352120033 = 54565154086120359552658077696 := by
  rw [← show ((([(3, 1), (13, 1), (54037, 1), (18798704059, 1), (2238169845409, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_13, prime_seventyFiveBU_54037, prime_seventyFiveBU_18798704059, prime_seventyFiveBU_2238169845409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120034 : Nat.totient 88670016307711676063352120034 = 42001586671308199172082269424 := by
  rw [← show ((([(2, 1), (19, 1), (54850141189, 1), (42541758894320687, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_19, prime_seventyFiveBU_54850141189, prime_seventyFiveBU_42541758894320687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120035 : Nat.totient 88670016307711676063352120035 = 70591041350047975446860352000 := by
  rw [← show ((([(5, 1), (401, 1), (421, 1), (105046192485190439653067, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_401, prime_seventyFiveBU_421, prime_seventyFiveBU_105046192485190439653067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120036 : Nat.totient 88670016307711676063352120036 = 25334290373631907446672034272 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1055595432234662810278001429, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_7, prime_seventyFiveBU_1055595432234662810278001429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120037 : Nat.totient 88670016307711676063352120037 = 83974988827044287231722848000 := by
  rw [← show ((([(23, 1), (101, 1), (1425649, 1), (26774105155577191831, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_23, prime_seventyFiveBU_101, prime_seventyFiveBU_1425649, prime_seventyFiveBU_26774105155577191831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120038 : Nat.totient 88670016307711676063352120038 = 38338316807188603496630169600 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (67, 1), (463, 1), (40433, 1), (284309737, 1), (364593499, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_11, prime_seventyFiveBU_31, prime_seventyFiveBU_67, prime_seventyFiveBU_463, prime_seventyFiveBU_40433, prime_seventyFiveBU_284309737, prime_seventyFiveBU_364593499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120039 : Nat.totient 88670016307711676063352120039 = 59113344205141117375568080020 := by
  rw [← show ((([(3, 2), (9852224034190186229261346671, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_9852224034190186229261346671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120040 : Nat.totient 88670016307711676063352120040 = 35207618037110401726449792000 := by
  rw [← show ((([(2, 3), (5, 1), (151, 1), (1511, 1), (24919, 1), (45707, 1), (8530255868077, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_151, prime_seventyFiveBU_1511, prime_seventyFiveBU_24919, prime_seventyFiveBU_45707, prime_seventyFiveBU_8530255868077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120041 : Nat.totient 88670016307711676063352120041 = 83454132995493342177272583552 := by
  rw [← show ((([(17, 1), (5215883312218333886079536473, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_17, prime_seventyFiveBU_5215883312218333886079536473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120042 : Nat.totient 88670016307711676063352120042 = 29556581783416822914625227360 := by
  rw [← show ((([(2, 1), (3, 1), (327247, 1), (45159576867886579079081, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_327247, prime_seventyFiveBU_45159576867886579079081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120043 : Nat.totient 88670016307711676063352120043 = 74344069301345618210471936736 := by
  rw [← show ((([(7, 1), (47, 1), (1783, 1), (151157446651184994490949, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_7, prime_seventyFiveBU_47, prime_seventyFiveBU_1783, prime_seventyFiveBU_151157446651184994490949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120044 : Nat.totient 88670016307711676063352120044 = 44332945839260818136688003840 := by
  rw [← show ((([(2, 2), (21499, 1), (353880169, 1), (2913683075424281, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_21499, prime_seventyFiveBU_353880169, prime_seventyFiveBU_2913683075424281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120045 : Nat.totient 88670016307711676063352120045 = 46487726179578591303528787200 := by
  rw [← show ((([(3, 1), (5, 1), (59, 1), (32917, 1), (3043780077840419245301, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_59, prime_seventyFiveBU_32917, prime_seventyFiveBU_3043780077840419245301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120046 : Nat.totient 88670016307711676063352120046 = 39944909974479991693675223040 := by
  rw [← show ((([(2, 1), (13, 1), (43, 1), (2153, 1), (4271, 1), (705833, 1), (12219668499943, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_13, prime_seventyFiveBU_43, prime_seventyFiveBU_2153, prime_seventyFiveBU_4271, prime_seventyFiveBU_705833, prime_seventyFiveBU_12219668499943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120047 : Nat.totient 88670016307711676063352120047 = 88670011374985146732771485616 := by
  rw [← show ((([(17975863, 1), (4932726529330562658569, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_17975863, prime_seventyFiveBU_4932726529330562658569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120048 : Nat.totient 88670016307711676063352120048 = 29551449396213851095513497600 := by
  rw [← show ((([(2, 4), (3, 3), (6359, 1), (84047, 1), (169241, 1), (768161, 1), (2954093, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_6359, prime_seventyFiveBU_84047, prime_seventyFiveBU_169241, prime_seventyFiveBU_768161, prime_seventyFiveBU_2954093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120049 : Nat.totient 88670016307711676063352120049 = 80592419933054966106394400400 := by
  rw [← show ((([(11, 1), (4831, 1), (1668580122837576938020589, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_11, prime_seventyFiveBU_4831, prime_seventyFiveBU_1668580122837576938020589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120050 : Nat.totient 88670016307711676063352120050 = 30394413601081392177026369280 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (4517, 1), (6811213, 1), (8234442318267383, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_7, prime_seventyFiveBU_4517, prime_seventyFiveBU_6811213, prime_seventyFiveBU_8234442318267383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120051 : Nat.totient 88670016307711676063352120051 = 57884122088280487827864175104 := by
  rw [← show ((([(3, 1), (73, 1), (139, 1), (492536873, 1), (5913970099176707, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_73, prime_seventyFiveBU_139, prime_seventyFiveBU_492536873, prime_seventyFiveBU_5913970099176707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120052 : Nat.totient 88670016307711676063352120052 = 43764360993222899266342192640 := by
  rw [← show ((([(2, 2), (107, 1), (281, 1), (56947195463, 1), (12946559112953, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_107, prime_seventyFiveBU_281, prime_seventyFiveBU_56947195463, prime_seventyFiveBU_12946559112953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120053 : Nat.totient 88670016307711676063352120053 = 83897491476820307782753281024 := by
  rw [← show ((([(19, 1), (1009, 1), (4027, 1), (52859, 1), (72235213, 1), (300803227, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_19, prime_seventyFiveBU_1009, prime_seventyFiveBU_4027, prime_seventyFiveBU_52859, prime_seventyFiveBU_72235213, prime_seventyFiveBU_300803227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120054 : Nat.totient 88670016307711676063352120054 = 28537411867071604115617967360 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (446003, 1), (43185431, 1), (26457725223497, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_29, prime_seventyFiveBU_446003, prime_seventyFiveBU_43185431, prime_seventyFiveBU_26457725223497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120055 : Nat.totient 88670016307711676063352120055 = 70933118705869113363266201088 := by
  rw [← show ((([(5, 1), (24509, 1), (1265864983, 1), (571602087046513, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_24509, prime_seventyFiveBU_1265864983, prime_seventyFiveBU_571602087046513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120056 : Nat.totient 88670016307711676063352120056 = 43131130220130201517374668800 := by
  rw [← show ((([(2, 3), (41, 1), (389, 1), (3803, 1), (182737221779512247681, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_41, prime_seventyFiveBU_389, prime_seventyFiveBU_3803, prime_seventyFiveBU_182737221779512247681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120057 : Nat.totient 88670016307711676063352120057 = 49954919069640429388571207040 := by
  rw [← show ((([(3, 2), (7, 2), (71, 1), (2536393, 1), (1116511766274447359, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_7, prime_seventyFiveBU_71, prime_seventyFiveBU_2536393, prime_seventyFiveBU_1116511766274447359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120058 : Nat.totient 88670016307711676063352120058 = 41725695111392932960406456832 := by
  rw [← show ((([(2, 1), (17, 1), (30427, 1), (11987434127, 1), (7150106376953, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_17, prime_seventyFiveBU_30427, prime_seventyFiveBU_11987434127, prime_seventyFiveBU_7150106376953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120059 : Nat.totient 88670016307711676063352120059 = 81849072230297261873468320320 := by
  rw [← show ((([(13, 1), (471503, 1), (14466017151976955536681, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_13, prime_seventyFiveBU_471503, prime_seventyFiveBU_14466017151976955536681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120060 : Nat.totient 88670016307711676063352120060 = 20550033927970070660245401600 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (3779, 1), (4999, 1), (13037, 1), (23717413349621, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_11, prime_seventyFiveBU_23, prime_seventyFiveBU_3779, prime_seventyFiveBU_4999, prime_seventyFiveBU_13037, prime_seventyFiveBU_23717413349621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120061 : Nat.totient 88670016307711676063352120061 = 88512520719243271665371032252 := by
  rw [← show ((([(563, 1), (157495588468404397981087247, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_563, prime_seventyFiveBU_157495588468404397981087247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120062 : Nat.totient 88670016307711676063352120062 = 44207973746538199527287303064 := by
  rw [← show ((([(2, 1), (349, 1), (127034407317638504388756619, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_349, prime_seventyFiveBU_127034407317638504388756619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120063 : Nat.totient 88670016307711676063352120063 = 57997996444702622203750486944 := by
  rw [← show ((([(3, 1), (53, 1), (35292319, 1), (15801541931519635903, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_53, prime_seventyFiveBU_35292319, prime_seventyFiveBU_15801541931519635903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120064 : Nat.totient 88670016307711676063352120064 = 37760163458942789251784331264 := by
  rw [← show ((([(2, 8), (7, 1), (163, 1), (4643, 1), (65381140929877709213, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_7, prime_seventyFiveBU_163, prime_seventyFiveBU_4643, prime_seventyFiveBU_65381140929877709213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120065 : Nat.totient 88670016307711676063352120065 = 70833269785689449683957684224 := by
  rw [← show ((([(5, 1), (709, 1), (26633, 1), (2162197, 1), (434355374166557, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_709, prime_seventyFiveBU_26633, prime_seventyFiveBU_2162197, prime_seventyFiveBU_434355374166557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120066 : Nat.totient 88670016307711676063352120066 = 29358304184314626443847939840 := by
  rw [← show ((([(2, 1), (3, 2), (149, 1), (32836511, 1), (335374499, 1), (3002140217, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_149, prime_seventyFiveBU_32836511, prime_seventyFiveBU_335374499, prime_seventyFiveBU_3002140217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120067 : Nat.totient 88670016307711676063352120067 = 87497975180319741821310194304 := by
  rw [← show ((([(79, 1), (1879, 1), (28753, 1), (20774938776647807179, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_79, prime_seventyFiveBU_1879, prime_seventyFiveBU_28753, prime_seventyFiveBU_20774938776647807179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120068 : Nat.totient 88670016307711676063352120068 = 43136764451625672675423618048 := by
  rw [← show ((([(2, 2), (37, 1), (180781709, 1), (3314061666542065249, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_37, prime_seventyFiveBU_180781709, prime_seventyFiveBU_3314061666542065249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120069 : Nat.totient 88670016307711676063352120069 = 57201331049413936430244742080 := by
  rw [← show ((([(3, 1), (31, 1), (11149, 1), (85518076559941897545517, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_31, prime_seventyFiveBU_11149, prime_seventyFiveBU_85518076559941897545517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120070 : Nat.totient 88670016307711676063352120070 = 35459272635786135690688754400 := by
  rw [← show ((([(2, 1), (5, 1), (4091, 1), (552991, 1), (3919487156506291547, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_4091, prime_seventyFiveBU_552991, prime_seventyFiveBU_3919487156506291547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120071 : Nat.totient 88670016307711676063352120071 = 68786213870291999106783744000 := by
  rw [← show ((([(7, 1), (11, 1), (271, 1), (1319, 1), (436097, 1), (7387353436417291, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_7, prime_seventyFiveBU_11, prime_seventyFiveBU_271, prime_seventyFiveBU_1319, prime_seventyFiveBU_436097, prime_seventyFiveBU_7387353436417291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120072 : Nat.totient 88670016307711676063352120072 = 25459433440976472281869713408 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (19, 1), (89, 1), (277, 1), (5309, 1), (182059, 1), (392279, 1), (1600217, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_13, prime_seventyFiveBU_19, prime_seventyFiveBU_89, prime_seventyFiveBU_277, prime_seventyFiveBU_5309, prime_seventyFiveBU_182059, prime_seventyFiveBU_392279, prime_seventyFiveBU_1600217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120073 : Nat.totient 88670016307711676063352120073 = 88670016261117963441247924240 := by
  rw [← show ((([(1903046813, 1), (46593712620201149021, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_1903046813, prime_seventyFiveBU_46593712620201149021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120074 : Nat.totient 88670016307711676063352120074 = 44333825540071691859784756416 := by
  rw [← show ((([(2, 1), (37489, 1), (1182613784146171891266133, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_37489, prime_seventyFiveBU_1182613784146171891266133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120075 : Nat.totient 88670016307711676063352120075 = 44508870930929782494545360640 := by
  rw [← show ((([(3, 4), (5, 2), (17, 1), (2575744845539917968434339, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_17, prime_seventyFiveBU_2575744845539917968434339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120076 : Nat.totient 88670016307711676063352120076 = 44284020447807710870356879872 := by
  rw [← show ((([(2, 2), (929, 1), (13567, 1), (1758803244157542645533, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_929, prime_seventyFiveBU_13567, prime_seventyFiveBU_1758803244157542645533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120077 : Nat.totient 88670016307711676063352120077 = 88526768757831506152386473904 := by
  rw [← show ((([(619, 1), (252446429, 1), (567436028990942227, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_619, prime_seventyFiveBU_252446429, prime_seventyFiveBU_567436028990942227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120078 : Nat.totient 88670016307711676063352120078 = 25029057707898148248094594272 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (83, 1), (99482087, 1), (255684568737270479, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_7, prime_seventyFiveBU_83, prime_seventyFiveBU_99482087, prime_seventyFiveBU_255684568737270479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120079 : Nat.totient 88670016307711676063352120079 = 87216409482995091209854544280 := by
  rw [← show ((([(61, 1), (1453606824716584853497575739, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_61, prime_seventyFiveBU_1453606824716584853497575739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120080 : Nat.totient 88670016307711676063352120080 = 35360852424772561432273566720 := by
  rw [← show ((([(2, 4), (5, 1), (331, 1), (750233247103, 1), (4463366004457, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_331, prime_seventyFiveBU_750233247103, prime_seventyFiveBU_4463366004457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120081 : Nat.totient 88670016307711676063352120081 = 59113314365309301354267080448 := by
  rw [← show ((([(3, 1), (2429617, 1), (10729309, 1), (1133824828543559, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_2429617, prime_seventyFiveBU_10729309, prime_seventyFiveBU_1133824828543559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120082 : Nat.totient 88670016307711676063352120082 = 40266894335807350980238288000 := by
  rw [← show ((([(2, 1), (11, 1), (1151, 1), (20393, 1), (60383, 1), (2843694764652899, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_11, prime_seventyFiveBU_1151, prime_seventyFiveBU_20393, prime_seventyFiveBU_60383, prime_seventyFiveBU_2843694764652899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120083 : Nat.totient 88670016307711676063352120083 = 81890149993328924220427144768 := by
  rw [← show ((([(23, 1), (29, 1), (132938555183975526331862249, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_23, prime_seventyFiveBU_29, prime_seventyFiveBU_132938555183975526331862249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120084 : Nat.totient 88670016307711676063352120084 = 29556662173498818922357889280 := by
  rw [← show ((([(2, 2), (3, 2), (2976781, 1), (827422644980449202449, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_2976781, prime_seventyFiveBU_827422644980449202449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120085 : Nat.totient 88670016307711676063352120085 = 56125193409645326966135934720 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (15063991, 1), (12936754723249996757, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_7, prime_seventyFiveBU_13, prime_seventyFiveBU_15063991, prime_seventyFiveBU_12936754723249996757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120086 : Nat.totient 88670016307711676063352120086 = 44335008153855838031676060042 := by
  rw [← show ((([(2, 1), (44335008153855838031676060043, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_44335008153855838031676060043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120087 : Nat.totient 88670016307711676063352120087 = 59113344204832504707713573568 := by
  rw [← show ((([(3, 1), (191545661413, 1), (154306142381591833, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_191545661413, prime_seventyFiveBU_154306142381591833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120088 : Nat.totient 88670016307711676063352120088 = 44334701443304073200906035200 := by
  rw [← show ((([(2, 3), (163433, 1), (2255161, 1), (2810641, 1), (10699515667, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_163433, prime_seventyFiveBU_2255161, prime_seventyFiveBU_2810641, prime_seventyFiveBU_10699515667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120089 : Nat.totient 88670016307711676063352120089 = 85882137920145263193872256000 := by
  rw [← show ((([(43, 1), (193, 1), (311, 1), (743111791, 1), (46231340094211, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_43, prime_seventyFiveBU_193, prime_seventyFiveBU_311, prime_seventyFiveBU_743111791, prime_seventyFiveBU_46231340094211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120090 : Nat.totient 88670016307711676063352120090 = 23142245390948862972562822464 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (47, 1), (62886536388447997208051149, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_5, prime_seventyFiveBU_47, prime_seventyFiveBU_62886536388447997208051149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120091 : Nat.totient 88670016307711676063352120091 = 83928370874562731863685569032 := by
  rw [← show ((([(19, 1), (1123, 1), (4155692754731765293309843, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_19, prime_seventyFiveBU_1123, prime_seventyFiveBU_4155692754731765293309843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120092 : Nat.totient 88670016307711676063352120092 = 35687794281449536623639527424 := by
  rw [← show ((([(2, 2), (7, 1), (17, 1), (457, 1), (3626964073, 1), (112385525820097, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_7, prime_seventyFiveBU_17, prime_seventyFiveBU_457, prime_seventyFiveBU_3626964073, prime_seventyFiveBU_112385525820097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120093 : Nat.totient 88670016307711676063352120093 = 53329071202849047937918672800 := by
  rw [← show ((([(3, 2), (11, 1), (131, 1), (493043, 1), (13867095319712464279, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_11, prime_seventyFiveBU_131, prime_seventyFiveBU_493043, prime_seventyFiveBU_13867095319712464279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120094 : Nat.totient 88670016307711676063352120094 = 44283175374964100817714481152 := by
  rw [← show ((([(2, 1), (859, 1), (201953, 1), (38383237, 1), (6658274905753, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_859, prime_seventyFiveBU_201953, prime_seventyFiveBU_38383237, prime_seventyFiveBU_6658274905753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120095 : Nat.totient 88670016307711676063352120095 = 70936013046169340850681696072 := by
  rw [← show ((([(5, 1), (17734003261542335212670424019, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_5, prime_seventyFiveBU_17734003261542335212670424019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120096 : Nat.totient 88670016307711676063352120096 = 29555771813746779123053861120 := by
  rw [← show ((([(2, 5), (3, 1), (32831, 1), (1366253183, 1), (20591607782387, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_3, prime_seventyFiveBU_32831, prime_seventyFiveBU_1366253183, prime_seventyFiveBU_20591607782387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120097 : Nat.totient 88670016307711676063352120097 = 86507298846546884171914583040 := by
  rw [← show ((([(41, 1), (2534153, 1), (853414661458220384689, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_41, prime_seventyFiveBU_2534153, prime_seventyFiveBU_853414661458220384689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120098 : Nat.totient 88670016307711676063352120098 = 40916356979945014812437107200 := by
  rw [← show ((([(2, 1), (13, 1), (4951, 1), (68269974419, 1), (10089758557217, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_13, prime_seventyFiveBU_4951, prime_seventyFiveBU_68269974419, prime_seventyFiveBU_10089758557217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120099 : Nat.totient 88670016307711676063352120099 = 50339425001195719135863926784 := by
  rw [← show ((([(3, 1), (7, 1), (157, 1), (8573, 1), (90977, 1), (34482076082226527, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_3, prime_seventyFiveBU_7, prime_seventyFiveBU_157, prime_seventyFiveBU_8573, prime_seventyFiveBU_90977, prime_seventyFiveBU_34482076082226527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120100 : Nat.totient 88670016307711676063352120100 = 34150517940623798075640537600 := by
  rw [← show ((([(2, 2), (5, 2), (31, 1), (199, 1), (38917, 1), (3693368694463370437, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_2, prime_seventyFiveBU_5, prime_seventyFiveBU_31, prime_seventyFiveBU_199, prime_seventyFiveBU_38917, prime_seventyFiveBU_3693368694463370437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventyFiveBU_88670016307711676063352120101 : Nat.totient 88670016307711676063352120101 = 88670016307711676063352120100 := by
  rw [← show ((([(88670016307711676063352120101, 1)] : List FactorBlock).map factorBlockValue).prod) = 88670016307711676063352120101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventyFiveBU_88670016307711676063352120101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventyFiveBU : certifiedKill 1 88670016307711676063352119999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventyFiveBU_88670016307711676063352120000, phi_seventyFiveBU_88670016307711676063352120001, phi_seventyFiveBU_88670016307711676063352120002,
    phi_seventyFiveBU_88670016307711676063352120003, phi_seventyFiveBU_88670016307711676063352120004, phi_seventyFiveBU_88670016307711676063352120005,
    phi_seventyFiveBU_88670016307711676063352120006, phi_seventyFiveBU_88670016307711676063352120007, phi_seventyFiveBU_88670016307711676063352120008,
    phi_seventyFiveBU_88670016307711676063352120009, phi_seventyFiveBU_88670016307711676063352120010, phi_seventyFiveBU_88670016307711676063352120011,
    phi_seventyFiveBU_88670016307711676063352120012, phi_seventyFiveBU_88670016307711676063352120013, phi_seventyFiveBU_88670016307711676063352120014,
    phi_seventyFiveBU_88670016307711676063352120015, phi_seventyFiveBU_88670016307711676063352120016, phi_seventyFiveBU_88670016307711676063352120017,
    phi_seventyFiveBU_88670016307711676063352120018, phi_seventyFiveBU_88670016307711676063352120019, phi_seventyFiveBU_88670016307711676063352120020,
    phi_seventyFiveBU_88670016307711676063352120021, phi_seventyFiveBU_88670016307711676063352120022, phi_seventyFiveBU_88670016307711676063352120023,
    phi_seventyFiveBU_88670016307711676063352120024, phi_seventyFiveBU_88670016307711676063352120025, phi_seventyFiveBU_88670016307711676063352120026,
    phi_seventyFiveBU_88670016307711676063352120027, phi_seventyFiveBU_88670016307711676063352120028, phi_seventyFiveBU_88670016307711676063352120029,
    phi_seventyFiveBU_88670016307711676063352120030, phi_seventyFiveBU_88670016307711676063352120031, phi_seventyFiveBU_88670016307711676063352120032,
    phi_seventyFiveBU_88670016307711676063352120033, phi_seventyFiveBU_88670016307711676063352120034, phi_seventyFiveBU_88670016307711676063352120035,
    phi_seventyFiveBU_88670016307711676063352120036, phi_seventyFiveBU_88670016307711676063352120037, phi_seventyFiveBU_88670016307711676063352120038,
    phi_seventyFiveBU_88670016307711676063352120039, phi_seventyFiveBU_88670016307711676063352120040, phi_seventyFiveBU_88670016307711676063352120041,
    phi_seventyFiveBU_88670016307711676063352120042, phi_seventyFiveBU_88670016307711676063352120043, phi_seventyFiveBU_88670016307711676063352120044,
    phi_seventyFiveBU_88670016307711676063352120045, phi_seventyFiveBU_88670016307711676063352120046, phi_seventyFiveBU_88670016307711676063352120047,
    phi_seventyFiveBU_88670016307711676063352120048, phi_seventyFiveBU_88670016307711676063352120049, phi_seventyFiveBU_88670016307711676063352120050,
    phi_seventyFiveBU_88670016307711676063352120051, phi_seventyFiveBU_88670016307711676063352120052, phi_seventyFiveBU_88670016307711676063352120053,
    phi_seventyFiveBU_88670016307711676063352120054, phi_seventyFiveBU_88670016307711676063352120055, phi_seventyFiveBU_88670016307711676063352120056,
    phi_seventyFiveBU_88670016307711676063352120057, phi_seventyFiveBU_88670016307711676063352120058, phi_seventyFiveBU_88670016307711676063352120059,
    phi_seventyFiveBU_88670016307711676063352120060, phi_seventyFiveBU_88670016307711676063352120061, phi_seventyFiveBU_88670016307711676063352120062,
    phi_seventyFiveBU_88670016307711676063352120063, phi_seventyFiveBU_88670016307711676063352120064, phi_seventyFiveBU_88670016307711676063352120065,
    phi_seventyFiveBU_88670016307711676063352120066, phi_seventyFiveBU_88670016307711676063352120067, phi_seventyFiveBU_88670016307711676063352120068,
    phi_seventyFiveBU_88670016307711676063352120069, phi_seventyFiveBU_88670016307711676063352120070, phi_seventyFiveBU_88670016307711676063352120071,
    phi_seventyFiveBU_88670016307711676063352120072, phi_seventyFiveBU_88670016307711676063352120073, phi_seventyFiveBU_88670016307711676063352120074,
    phi_seventyFiveBU_88670016307711676063352120075, phi_seventyFiveBU_88670016307711676063352120076, phi_seventyFiveBU_88670016307711676063352120077,
    phi_seventyFiveBU_88670016307711676063352120078, phi_seventyFiveBU_88670016307711676063352120079, phi_seventyFiveBU_88670016307711676063352120080,
    phi_seventyFiveBU_88670016307711676063352120081, phi_seventyFiveBU_88670016307711676063352120082, phi_seventyFiveBU_88670016307711676063352120083,
    phi_seventyFiveBU_88670016307711676063352120084, phi_seventyFiveBU_88670016307711676063352120085, phi_seventyFiveBU_88670016307711676063352120086,
    phi_seventyFiveBU_88670016307711676063352120087, phi_seventyFiveBU_88670016307711676063352120088, phi_seventyFiveBU_88670016307711676063352120089,
    phi_seventyFiveBU_88670016307711676063352120090, phi_seventyFiveBU_88670016307711676063352120091, phi_seventyFiveBU_88670016307711676063352120092,
    phi_seventyFiveBU_88670016307711676063352120093, phi_seventyFiveBU_88670016307711676063352120094, phi_seventyFiveBU_88670016307711676063352120095,
    phi_seventyFiveBU_88670016307711676063352120096, phi_seventyFiveBU_88670016307711676063352120097, phi_seventyFiveBU_88670016307711676063352120098,
    phi_seventyFiveBU_88670016307711676063352120099, phi_seventyFiveBU_88670016307711676063352120100, phi_seventyFiveBU_88670016307711676063352120101]

end TotientTailPeriodKiller
end Erdos249257
