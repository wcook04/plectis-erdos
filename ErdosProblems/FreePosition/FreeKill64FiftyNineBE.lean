import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 59P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyNineBEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyNineBEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyNineBEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyNineBEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyNineBEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyNineBEFastPow a n * fiftyNineBEFastPow a n * a
        else fiftyNineBEFastPow a n * fiftyNineBEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyNineBE_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyNineBE_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyNineBE_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyNineBE_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyNineBE_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyNineBE_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyNineBE_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyNineBE_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyNineBE_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyNineBE_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyNineBE_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyNineBE_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyNineBE_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyNineBE_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyNineBE_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyNineBE_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyNineBE_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyNineBE_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyNineBE_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyNineBE_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyNineBE_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyNineBE_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyNineBE_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyNineBE_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyNineBE_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyNineBE_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyNineBE_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyNineBE_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyNineBE_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyNineBE_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyNineBE_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyNineBE_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyNineBE_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyNineBE_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyNineBE_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyNineBE_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyNineBE_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyNineBE_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyNineBE_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyNineBE_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyNineBE_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyNineBE_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyNineBE_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyNineBE_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyNineBE_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyNineBE_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyNineBE_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyNineBE_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyNineBE_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyNineBE_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyNineBE_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyNineBE_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyNineBE_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyNineBE_281 : Nat.Prime 281 := by norm_num
private theorem prime_fiftyNineBE_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyNineBE_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftyNineBE_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyNineBE_313 : Nat.Prime 313 := by norm_num
private theorem prime_fiftyNineBE_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyNineBE_349 : Nat.Prime 349 := by norm_num
private theorem prime_fiftyNineBE_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftyNineBE_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyNineBE_367 : Nat.Prime 367 := by norm_num
private theorem prime_fiftyNineBE_373 : Nat.Prime 373 := by norm_num
private theorem prime_fiftyNineBE_379 : Nat.Prime 379 := by norm_num
private theorem prime_fiftyNineBE_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyNineBE_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftyNineBE_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyNineBE_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyNineBE_431 : Nat.Prime 431 := by norm_num
private theorem prime_fiftyNineBE_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftyNineBE_443 : Nat.Prime 443 := by norm_num
private theorem prime_fiftyNineBE_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftyNineBE_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftyNineBE_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftyNineBE_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyNineBE_487 : Nat.Prime 487 := by norm_num
private theorem prime_fiftyNineBE_499 : Nat.Prime 499 := by norm_num
private theorem prime_fiftyNineBE_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftyNineBE_509 : Nat.Prime 509 := by norm_num
private theorem prime_fiftyNineBE_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyNineBE_523 : Nat.Prime 523 := by norm_num
private theorem prime_fiftyNineBE_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyNineBE_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyNineBE_571 : Nat.Prime 571 := by norm_num
private theorem prime_fiftyNineBE_593 : Nat.Prime 593 := by norm_num
private theorem prime_fiftyNineBE_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftyNineBE_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftyNineBE_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftyNineBE_641 : Nat.Prime 641 := by norm_num
private theorem prime_fiftyNineBE_643 : Nat.Prime 643 := by norm_num
private theorem prime_fiftyNineBE_653 : Nat.Prime 653 := by norm_num
private theorem prime_fiftyNineBE_659 : Nat.Prime 659 := by norm_num
private theorem prime_fiftyNineBE_673 : Nat.Prime 673 := by norm_num
private theorem prime_fiftyNineBE_709 : Nat.Prime 709 := by norm_num
private theorem prime_fiftyNineBE_739 : Nat.Prime 739 := by norm_num
private theorem prime_fiftyNineBE_769 : Nat.Prime 769 := by norm_num
private theorem prime_fiftyNineBE_773 : Nat.Prime 773 := by norm_num
private theorem prime_fiftyNineBE_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyNineBE_821 : Nat.Prime 821 := by norm_num
private theorem prime_fiftyNineBE_829 : Nat.Prime 829 := by norm_num
private theorem prime_fiftyNineBE_863 : Nat.Prime 863 := by norm_num
private theorem prime_fiftyNineBE_883 : Nat.Prime 883 := by norm_num
private theorem prime_fiftyNineBE_953 : Nat.Prime 953 := by norm_num
private theorem prime_fiftyNineBE_967 : Nat.Prime 967 := by norm_num
private theorem prime_fiftyNineBE_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftyNineBE_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_fiftyNineBE_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fiftyNineBE_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_fiftyNineBE_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_fiftyNineBE_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fiftyNineBE_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fiftyNineBE_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_fiftyNineBE_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_fiftyNineBE_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fiftyNineBE_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_fiftyNineBE_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_fiftyNineBE_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_fiftyNineBE_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyNineBE_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_fiftyNineBE_1571 : Nat.Prime 1571 := by norm_num
private theorem prime_fiftyNineBE_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_fiftyNineBE_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fiftyNineBE_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_fiftyNineBE_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fiftyNineBE_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fiftyNineBE_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_fiftyNineBE_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_fiftyNineBE_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_fiftyNineBE_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_fiftyNineBE_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_fiftyNineBE_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_fiftyNineBE_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_fiftyNineBE_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_fiftyNineBE_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_fiftyNineBE_2153 : Nat.Prime 2153 := by norm_num
private theorem prime_fiftyNineBE_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_fiftyNineBE_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_fiftyNineBE_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_fiftyNineBE_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_fiftyNineBE_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_fiftyNineBE_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_fiftyNineBE_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_fiftyNineBE_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_fiftyNineBE_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_fiftyNineBE_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_fiftyNineBE_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_fiftyNineBE_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_fiftyNineBE_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_fiftyNineBE_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fiftyNineBE_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_fiftyNineBE_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_fiftyNineBE_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_fiftyNineBE_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_fiftyNineBE_3191 : Nat.Prime 3191 := by norm_num
private theorem prime_fiftyNineBE_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_fiftyNineBE_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_fiftyNineBE_3359 : Nat.Prime 3359 := by norm_num
private theorem prime_fiftyNineBE_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_fiftyNineBE_3457 : Nat.Prime 3457 := by norm_num
private theorem prime_fiftyNineBE_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_fiftyNineBE_3607 : Nat.Prime 3607 := by norm_num
private theorem prime_fiftyNineBE_3659 : Nat.Prime 3659 := by norm_num
private theorem prime_fiftyNineBE_3671 : Nat.Prime 3671 := by norm_num
private theorem prime_fiftyNineBE_3673 : Nat.Prime 3673 := by norm_num
private theorem prime_fiftyNineBE_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_fiftyNineBE_3697 : Nat.Prime 3697 := by norm_num
private theorem prime_fiftyNineBE_3853 : Nat.Prime 3853 := by norm_num
private theorem prime_fiftyNineBE_4003 : Nat.Prime 4003 := by norm_num
private theorem prime_fiftyNineBE_4057 : Nat.Prime 4057 := by norm_num
private theorem prime_fiftyNineBE_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_fiftyNineBE_4363 : Nat.Prime 4363 := by norm_num
private theorem prime_fiftyNineBE_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_fiftyNineBE_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_fiftyNineBE_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_fiftyNineBE_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_fiftyNineBE_4507 : Nat.Prime 4507 := by norm_num
private theorem prime_fiftyNineBE_4547 : Nat.Prime 4547 := by norm_num
private theorem prime_fiftyNineBE_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_fiftyNineBE_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_fiftyNineBE_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_fiftyNineBE_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_fiftyNineBE_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_fiftyNineBE_6299 : Nat.Prime 6299 := by norm_num
private theorem prime_fiftyNineBE_6547 : Nat.Prime 6547 := by norm_num
private theorem prime_fiftyNineBE_6653 : Nat.Prime 6653 := by norm_num
private theorem prime_fiftyNineBE_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_fiftyNineBE_6823 : Nat.Prime 6823 := by norm_num
private theorem prime_fiftyNineBE_7127 : Nat.Prime 7127 := by norm_num
private theorem prime_fiftyNineBE_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_fiftyNineBE_7193 : Nat.Prime 7193 := by norm_num
private theorem prime_fiftyNineBE_7219 : Nat.Prime 7219 := by norm_num
private theorem prime_fiftyNineBE_7243 : Nat.Prime 7243 := by norm_num
private theorem prime_fiftyNineBE_7541 : Nat.Prime 7541 := by norm_num
private theorem prime_fiftyNineBE_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_fiftyNineBE_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_fiftyNineBE_7757 : Nat.Prime 7757 := by norm_num
private theorem prime_fiftyNineBE_8389 : Nat.Prime 8389 := by norm_num
private theorem prime_fiftyNineBE_8467 : Nat.Prime 8467 := by norm_num
private theorem prime_fiftyNineBE_8501 : Nat.Prime 8501 := by norm_num
private theorem prime_fiftyNineBE_8609 : Nat.Prime 8609 := by norm_num
private theorem prime_fiftyNineBE_8641 : Nat.Prime 8641 := by norm_num
private theorem prime_fiftyNineBE_8689 : Nat.Prime 8689 := by norm_num
private theorem prime_fiftyNineBE_8951 : Nat.Prime 8951 := by norm_num
private theorem prime_fiftyNineBE_9007 : Nat.Prime 9007 := by norm_num
private theorem prime_fiftyNineBE_9511 : Nat.Prime 9511 := by norm_num
private theorem prime_fiftyNineBE_9689 : Nat.Prime 9689 := by norm_num
private theorem prime_fiftyNineBE_10177 : Nat.Prime 10177 := by norm_num
private theorem prime_fiftyNineBE_10613 : Nat.Prime 10613 := by norm_num
private theorem prime_fiftyNineBE_11117 : Nat.Prime 11117 := by norm_num
private theorem prime_fiftyNineBE_11503 : Nat.Prime 11503 := by norm_num
private theorem prime_fiftyNineBE_11593 : Nat.Prime 11593 := by norm_num
private theorem prime_fiftyNineBE_11743 : Nat.Prime 11743 := by norm_num
private theorem prime_fiftyNineBE_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_fiftyNineBE_11953 : Nat.Prime 11953 := by norm_num
private theorem prime_fiftyNineBE_12157 : Nat.Prime 12157 := by norm_num
private theorem prime_fiftyNineBE_12689 : Nat.Prime 12689 := by norm_num
private theorem prime_fiftyNineBE_13033 : Nat.Prime 13033 := by norm_num
private theorem prime_fiftyNineBE_13339 : Nat.Prime 13339 := by norm_num
private theorem prime_fiftyNineBE_13397 : Nat.Prime 13397 := by norm_num
private theorem prime_fiftyNineBE_13417 : Nat.Prime 13417 := by norm_num
private theorem prime_fiftyNineBE_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_fiftyNineBE_14407 : Nat.Prime 14407 := by norm_num
private theorem prime_fiftyNineBE_14923 : Nat.Prime 14923 := by norm_num
private theorem prime_fiftyNineBE_15013 : Nat.Prime 15013 := by norm_num
private theorem prime_fiftyNineBE_15091 : Nat.Prime 15091 := by norm_num
private theorem prime_fiftyNineBE_16937 : Nat.Prime 16937 := by norm_num
private theorem prime_fiftyNineBE_18701 : Nat.Prime 18701 := by norm_num
private theorem prime_fiftyNineBE_20693 : Nat.Prime 20693 := by norm_num
private theorem prime_fiftyNineBE_21991 : Nat.Prime 21991 := by norm_num
private theorem prime_fiftyNineBE_22067 : Nat.Prime 22067 := by norm_num
private theorem prime_fiftyNineBE_22397 : Nat.Prime 22397 := by norm_num
private theorem prime_fiftyNineBE_22787 : Nat.Prime 22787 := by norm_num
private theorem prime_fiftyNineBE_23203 : Nat.Prime 23203 := by norm_num
private theorem prime_fiftyNineBE_23663 : Nat.Prime 23663 := by norm_num
private theorem prime_fiftyNineBE_24809 : Nat.Prime 24809 := by norm_num
private theorem prime_fiftyNineBE_25747 : Nat.Prime 25747 := by norm_num
private theorem prime_fiftyNineBE_26987 : Nat.Prime 26987 := by norm_num
private theorem prime_fiftyNineBE_27059 : Nat.Prime 27059 := by norm_num
private theorem prime_fiftyNineBE_28621 : Nat.Prime 28621 := by norm_num
private theorem prime_fiftyNineBE_29063 : Nat.Prime 29063 := by norm_num
private theorem prime_fiftyNineBE_29231 : Nat.Prime 29231 := by norm_num
private theorem prime_fiftyNineBE_30029 : Nat.Prime 30029 := by norm_num
private theorem prime_fiftyNineBE_30853 : Nat.Prime 30853 := by norm_num
private theorem prime_fiftyNineBE_30859 : Nat.Prime 30859 := by norm_num
private theorem prime_fiftyNineBE_31481 : Nat.Prime 31481 := by norm_num
private theorem prime_fiftyNineBE_31699 : Nat.Prime 31699 := by norm_num
private theorem prime_fiftyNineBE_32299 : Nat.Prime 32299 := by norm_num
private theorem prime_fiftyNineBE_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_fiftyNineBE_32479 : Nat.Prime 32479 := by norm_num
private theorem prime_fiftyNineBE_32909 : Nat.Prime 32909 := by norm_num
private theorem prime_fiftyNineBE_34123 : Nat.Prime 34123 := by norm_num
private theorem prime_fiftyNineBE_34421 : Nat.Prime 34421 := by norm_num
private theorem prime_fiftyNineBE_34519 : Nat.Prime 34519 := by norm_num
private theorem prime_fiftyNineBE_34747 : Nat.Prime 34747 := by norm_num
private theorem prime_fiftyNineBE_35593 : Nat.Prime 35593 := by norm_num
private theorem prime_fiftyNineBE_36563 : Nat.Prime 36563 := by norm_num
private theorem prime_fiftyNineBE_36793 : Nat.Prime 36793 := by norm_num
private theorem prime_fiftyNineBE_37021 : Nat.Prime 37021 := by norm_num
private theorem prime_fiftyNineBE_38183 : Nat.Prime 38183 := by norm_num
private theorem prime_fiftyNineBE_38231 : Nat.Prime 38231 := by norm_num
private theorem prime_fiftyNineBE_38273 : Nat.Prime 38273 := by norm_num
private theorem prime_fiftyNineBE_39313 : Nat.Prime 39313 := by norm_num
private theorem prime_fiftyNineBE_43753 : Nat.Prime 43753 := by norm_num
private theorem prime_fiftyNineBE_44179 : Nat.Prime 44179 := by norm_num
private theorem prime_fiftyNineBE_48281 : Nat.Prime 48281 := by norm_num
private theorem prime_fiftyNineBE_51673 : Nat.Prime 51673 := by norm_num
private theorem prime_fiftyNineBE_53959 : Nat.Prime 53959 := by norm_num
private theorem prime_fiftyNineBE_55351 : Nat.Prime 55351 := by norm_num
private theorem prime_fiftyNineBE_56611 : Nat.Prime 56611 := by norm_num
private theorem prime_fiftyNineBE_57809 : Nat.Prime 57809 := by norm_num
private theorem prime_fiftyNineBE_59093 : Nat.Prime 59093 := by norm_num
private theorem prime_fiftyNineBE_60497 : Nat.Prime 60497 := by norm_num
private theorem prime_fiftyNineBE_63337 : Nat.Prime 63337 := by norm_num
private theorem prime_fiftyNineBE_63559 : Nat.Prime 63559 := by norm_num
private theorem prime_fiftyNineBE_63743 : Nat.Prime 63743 := by norm_num
private theorem prime_fiftyNineBE_63773 : Nat.Prime 63773 := by norm_num
private theorem prime_fiftyNineBE_65809 : Nat.Prime 65809 := by norm_num
private theorem prime_fiftyNineBE_66463 : Nat.Prime 66463 := by norm_num
private theorem prime_fiftyNineBE_72109 : Nat.Prime 72109 := by norm_num
private theorem prime_fiftyNineBE_73673 : Nat.Prime 73673 := by norm_num
private theorem prime_fiftyNineBE_75731 : Nat.Prime 75731 := by norm_num
private theorem prime_fiftyNineBE_76079 : Nat.Prime 76079 := by norm_num
private theorem prime_fiftyNineBE_77587 : Nat.Prime 77587 := by norm_num
private theorem prime_fiftyNineBE_77719 : Nat.Prime 77719 := by norm_num
private theorem prime_fiftyNineBE_78877 : Nat.Prime 78877 := by norm_num
private theorem prime_fiftyNineBE_83407 : Nat.Prime 83407 := by norm_num
private theorem prime_fiftyNineBE_87407 : Nat.Prime 87407 := by norm_num
private theorem prime_fiftyNineBE_89917 : Nat.Prime 89917 := by norm_num
private theorem prime_fiftyNineBE_90007 : Nat.Prime 90007 := by norm_num
private theorem prime_fiftyNineBE_90149 : Nat.Prime 90149 := by norm_num
private theorem prime_fiftyNineBE_92203 : Nat.Prime 92203 := by norm_num
private theorem prime_fiftyNineBE_96263 : Nat.Prime 96263 := by norm_num
private theorem prime_fiftyNineBE_98411 : Nat.Prime 98411 := by norm_num
private theorem prime_fiftyNineBE_101963 : Nat.Prime 101963 := by norm_num
private theorem prime_fiftyNineBE_108631 : Nat.Prime 108631 := by norm_num
private theorem prime_fiftyNineBE_111791 : Nat.Prime 111791 := by norm_num
private theorem prime_fiftyNineBE_112459 : Nat.Prime 112459 := by norm_num
private theorem prime_fiftyNineBE_118387 : Nat.Prime 118387 := by norm_num
private theorem prime_fiftyNineBE_121321 : Nat.Prime 121321 := by norm_num
private theorem prime_fiftyNineBE_122393 : Nat.Prime 122393 := by norm_num
private theorem prime_fiftyNineBE_126653 : Nat.Prime 126653 := by norm_num
private theorem prime_fiftyNineBE_128047 : Nat.Prime 128047 := by norm_num
private theorem prime_fiftyNineBE_128147 : Nat.Prime 128147 := by norm_num
private theorem prime_fiftyNineBE_132911 : Nat.Prime 132911 := by norm_num
private theorem prime_fiftyNineBE_136987 : Nat.Prime 136987 := by norm_num
private theorem prime_fiftyNineBE_142297 : Nat.Prime 142297 := by norm_num
private theorem prime_fiftyNineBE_146291 : Nat.Prime 146291 := by norm_num
private theorem prime_fiftyNineBE_151847 : Nat.Prime 151847 := by norm_num
private theorem prime_fiftyNineBE_164789 : Nat.Prime 164789 := by norm_num
private theorem prime_fiftyNineBE_165709 : Nat.Prime 165709 := by norm_num
private theorem prime_fiftyNineBE_176051 : Nat.Prime 176051 := by norm_num
private theorem prime_fiftyNineBE_179833 : Nat.Prime 179833 := by norm_num
private theorem prime_fiftyNineBE_184337 : Nat.Prime 184337 := by norm_num
private theorem prime_fiftyNineBE_191563 : Nat.Prime 191563 := by norm_num
private theorem prime_fiftyNineBE_192091 : Nat.Prime 192091 := by norm_num
private theorem prime_fiftyNineBE_194101 : Nat.Prime 194101 := by norm_num
private theorem prime_fiftyNineBE_198533 : Nat.Prime 198533 := by norm_num
private theorem prime_fiftyNineBE_198659 : Nat.Prime 198659 := by norm_num
private theorem prime_fiftyNineBE_201151 : Nat.Prime 201151 := by norm_num
private theorem prime_fiftyNineBE_203351 : Nat.Prime 203351 := by norm_num
private theorem prime_fiftyNineBE_215843 : Nat.Prime 215843 := by norm_num
private theorem prime_fiftyNineBE_222361 : Nat.Prime 222361 := by norm_num
private theorem prime_fiftyNineBE_228523 : Nat.Prime 228523 := by norm_num
private theorem prime_fiftyNineBE_229549 : Nat.Prime 229549 := by norm_num
private theorem prime_fiftyNineBE_230563 : Nat.Prime 230563 := by norm_num
private theorem prime_fiftyNineBE_259733 : Nat.Prime 259733 := by norm_num
private theorem prime_fiftyNineBE_262783 : Nat.Prime 262783 := by norm_num
private theorem prime_fiftyNineBE_273719 : Nat.Prime 273719 := by norm_num
private theorem prime_fiftyNineBE_281581 : Nat.Prime 281581 := by norm_num
private theorem prime_fiftyNineBE_283553 : Nat.Prime 283553 := by norm_num
private theorem prime_fiftyNineBE_285049 : Nat.Prime 285049 := by norm_num
private theorem prime_fiftyNineBE_300583 : Nat.Prime 300583 := by norm_num
private theorem prime_fiftyNineBE_316937 : Nat.Prime 316937 := by norm_num
private theorem prime_fiftyNineBE_331613 : Nat.Prime 331613 := by norm_num
private theorem prime_fiftyNineBE_331711 : Nat.Prime 331711 := by norm_num
private theorem prime_fiftyNineBE_342373 : Nat.Prime 342373 := by norm_num
private theorem prime_fiftyNineBE_342647 : Nat.Prime 342647 := by norm_num
private theorem prime_fiftyNineBE_347099 : Nat.Prime 347099 := by norm_num
private theorem prime_fiftyNineBE_418993 : Nat.Prime 418993 := by norm_num
private theorem prime_fiftyNineBE_422309 : Nat.Prime 422309 := by norm_num
private theorem prime_fiftyNineBE_426707 : Nat.Prime 426707 := by norm_num
private theorem prime_fiftyNineBE_428227 : Nat.Prime 428227 := by norm_num
private theorem prime_fiftyNineBE_448907 : Nat.Prime 448907 := by norm_num
private theorem prime_fiftyNineBE_461119 : Nat.Prime 461119 := by norm_num
private theorem prime_fiftyNineBE_471061 : Nat.Prime 471061 := by norm_num
private theorem prime_fiftyNineBE_502861 : Nat.Prime 502861 := by norm_num
private theorem prime_fiftyNineBE_564301 : Nat.Prime 564301 := by norm_num
private theorem prime_fiftyNineBE_571069 : Nat.Prime 571069 := by norm_num
private theorem prime_fiftyNineBE_641713 : Nat.Prime 641713 := by norm_num
private theorem prime_fiftyNineBE_655331 : Nat.Prime 655331 := by norm_num
private theorem prime_fiftyNineBE_699383 : Nat.Prime 699383 := by norm_num
private theorem prime_fiftyNineBE_700027 : Nat.Prime 700027 := by norm_num
private theorem prime_fiftyNineBE_719189 : Nat.Prime 719189 := by norm_num
private theorem prime_fiftyNineBE_743401 : Nat.Prime 743401 := by norm_num
private theorem prime_fiftyNineBE_760657 : Nat.Prime 760657 := by norm_num
private theorem prime_fiftyNineBE_775639 : Nat.Prime 775639 := by norm_num
private theorem prime_fiftyNineBE_794579 : Nat.Prime 794579 := by norm_num
private theorem prime_fiftyNineBE_796009 : Nat.Prime 796009 := by norm_num
private theorem prime_fiftyNineBE_883061 : Nat.Prime 883061 := by norm_num
private theorem prime_fiftyNineBE_961643 : Nat.Prime 961643 := by norm_num
private theorem prime_fiftyNineBE_969559 : Nat.Prime 969559 := by norm_num
private theorem prime_fiftyNineBE_982603 : Nat.Prime 982603 := by norm_num
private theorem prime_fiftyNineBE_997333 : Nat.Prime 997333 := by norm_num
private theorem prime_fiftyNineBE_1204037 : Nat.Prime 1204037 := by norm_num
private theorem prime_fiftyNineBE_1221097 : Nat.Prime 1221097 := by norm_num
private theorem prime_fiftyNineBE_1326167 : Nat.Prime 1326167 := by norm_num
private theorem prime_fiftyNineBE_1349317 : Nat.Prime 1349317 := by norm_num
private theorem prime_fiftyNineBE_1350703 : Nat.Prime 1350703 := by norm_num
private theorem prime_fiftyNineBE_1434229 : Nat.Prime 1434229 := by norm_num
private theorem prime_fiftyNineBE_1449953 : Nat.Prime 1449953 := by norm_num
private theorem prime_fiftyNineBE_1558787 : Nat.Prime 1558787 := by norm_num
private theorem prime_fiftyNineBE_1572559 : Nat.Prime 1572559 := by norm_num
private theorem prime_fiftyNineBE_1667629 : Nat.Prime 1667629 := by norm_num
private theorem prime_fiftyNineBE_1718971 : Nat.Prime 1718971 := by norm_num
private theorem prime_fiftyNineBE_1754527 : Nat.Prime 1754527 := by norm_num
private theorem prime_fiftyNineBE_1778219 : Nat.Prime 1778219 := by norm_num
private theorem prime_fiftyNineBE_1818617 : Nat.Prime 1818617 := by norm_num
private theorem prime_fiftyNineBE_2008339 : Nat.Prime 2008339 := by norm_num
private theorem prime_fiftyNineBE_2018531 : Nat.Prime 2018531 := by norm_num
private theorem prime_fiftyNineBE_2048939 : Nat.Prime 2048939 := by norm_num
private theorem prime_fiftyNineBE_2122649 : Nat.Prime 2122649 := by norm_num
private theorem prime_fiftyNineBE_2244503 : Nat.Prime 2244503 := by norm_num
private theorem prime_fiftyNineBE_2302543 : Nat.Prime 2302543 := by norm_num
private theorem prime_fiftyNineBE_2323403 : Nat.Prime 2323403 := by norm_num
private theorem prime_fiftyNineBE_2396131 : Nat.Prime 2396131 := by norm_num
private theorem prime_fiftyNineBE_2596163 : Nat.Prime 2596163 := by norm_num
private theorem prime_fiftyNineBE_2608649 : Nat.Prime 2608649 := by norm_num
private theorem prime_fiftyNineBE_2650429 : Nat.Prime 2650429 := by norm_num
private theorem prime_fiftyNineBE_2664379 : Nat.Prime 2664379 := by norm_num
private theorem prime_fiftyNineBE_2744689 : Nat.Prime 2744689 := by norm_num
private theorem prime_fiftyNineBE_2904299 : Nat.Prime 2904299 := by norm_num
private theorem prime_fiftyNineBE_2915327 : Nat.Prime 2915327 := by norm_num
private theorem prime_fiftyNineBE_3055231 : Nat.Prime 3055231 := by norm_num
private theorem prime_fiftyNineBE_3368011 : Nat.Prime 3368011 := by norm_num
private theorem prime_fiftyNineBE_3409687 : Nat.Prime 3409687 := by norm_num
private theorem prime_fiftyNineBE_3922907 : Nat.Prime 3922907 := by norm_num
private theorem prime_fiftyNineBE_3984521 : Nat.Prime 3984521 := by norm_num
private theorem prime_fiftyNineBE_4181347 : Nat.Prime 4181347 := by norm_num
private theorem prime_fiftyNineBE_4241239 : Nat.Prime 4241239 := by norm_num
private theorem prime_fiftyNineBE_4308001 : Nat.Prime 4308001 := by norm_num
private theorem prime_fiftyNineBE_4583633 : Nat.Prime 4583633 := by norm_num
private theorem prime_fiftyNineBE_4654807 : Nat.Prime 4654807 := by norm_num
private theorem prime_fiftyNineBE_4684879 : Nat.Prime 4684879 := by norm_num
private theorem prime_fiftyNineBE_4800893 : Nat.Prime 4800893 := by norm_num
private theorem prime_fiftyNineBE_4898449 : Nat.Prime 4898449 := by norm_num
private theorem prime_fiftyNineBE_5126323 : Nat.Prime 5126323 := by norm_num
private theorem prime_fiftyNineBE_5643041 : Nat.Prime 5643041 := by norm_num
private theorem prime_fiftyNineBE_6103519 : Nat.Prime 6103519 := by norm_num
private theorem prime_fiftyNineBE_6724931 : Nat.Prime 6724931 := by norm_num
private theorem prime_fiftyNineBE_7016237 : Nat.Prime 7016237 := by norm_num
private theorem prime_fiftyNineBE_7589207 : Nat.Prime 7589207 := by norm_num
private theorem prime_fiftyNineBE_8270711 : Nat.Prime 8270711 := by norm_num
private theorem prime_fiftyNineBE_8335771 : Nat.Prime 8335771 := by norm_num
private theorem prime_fiftyNineBE_8603797 : Nat.Prime 8603797 := by norm_num
private theorem prime_fiftyNineBE_9134903 : Nat.Prime 9134903 := by norm_num
private theorem prime_fiftyNineBE_9144631 : Nat.Prime 9144631 := by norm_num
private theorem prime_fiftyNineBE_9769159 : Nat.Prime 9769159 := by norm_num
private theorem prime_fiftyNineBE_10505477 : Nat.Prime 10505477 := by norm_num
private theorem prime_fiftyNineBE_11596087 : Nat.Prime 11596087 := by norm_num
private theorem prime_fiftyNineBE_11803663 : Nat.Prime 11803663 := by norm_num
private theorem prime_fiftyNineBE_12922561 : Nat.Prime 12922561 := by norm_num
private theorem prime_fiftyNineBE_13037767 : Nat.Prime 13037767 := by norm_num
private theorem prime_fiftyNineBE_13529063 : Nat.Prime 13529063 := by norm_num
private theorem prime_fiftyNineBE_17087209 : Nat.Prime 17087209 := by norm_num
private theorem prime_fiftyNineBE_17093831 : Nat.Prime 17093831 := by norm_num
private theorem prime_fiftyNineBE_21731243 : Nat.Prime 21731243 := by norm_num
private theorem prime_fiftyNineBE_22210819 : Nat.Prime 22210819 := by norm_num
private theorem prime_fiftyNineBE_24805379 : Nat.Prime 24805379 := by norm_num
private theorem prime_fiftyNineBE_24867881 : Nat.Prime 24867881 := by norm_num
private theorem prime_fiftyNineBE_25420511 : Nat.Prime 25420511 := by norm_num
private theorem prime_fiftyNineBE_26584681 : Nat.Prime 26584681 := by norm_num
private theorem prime_fiftyNineBE_26623721 : Nat.Prime 26623721 := by norm_num
private theorem prime_fiftyNineBE_26932891 : Nat.Prime 26932891 := by norm_num
private theorem prime_fiftyNineBE_27464293 : Nat.Prime 27464293 := by norm_num
private theorem prime_fiftyNineBE_28937693 : Nat.Prime 28937693 := by norm_num
private theorem prime_fiftyNineBE_29973529 : Nat.Prime 29973529 := by norm_num
private theorem prime_fiftyNineBE_31672337 : Nat.Prime 31672337 := by
  apply lucas_primality 31672337 (3 : ZMod 31672337)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (48281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (48281, 1)] : List FactorBlock).map factorBlockValue).prod) = 31672337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_48281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31672337) ^ 15836168 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31672337) ^ 772496 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31672337) ^ 656 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_32316149 : Nat.Prime 32316149 := by
  apply lucas_primality 32316149 (2 : ZMod 32316149)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1051, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1051, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 32316149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_1051
      · exact prime_fiftyNineBE_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32316149) ^ 16158074 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32316149) ^ 30748 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32316149) ^ 4204 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34015703 : Nat.Prime 34015703 := by
  apply lucas_primality 34015703 (5 : ZMod 34015703)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (347099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (347099, 1)] : List FactorBlock).map factorBlockValue).prod) = 34015703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_347099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34015703) ^ 17007851 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34015703) ^ 4859386 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34015703) ^ 98 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34415189 : Nat.Prime 34415189 := by
  apply lucas_primality 34415189 (2 : ZMod 34415189)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8603797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8603797, 1)] : List FactorBlock).map factorBlockValue).prod) = 34415189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_8603797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34415189) ^ 17207594 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 34415189) ^ 4 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34480343 : Nat.Prime 34480343 := by
  apply lucas_primality 34480343 (5 : ZMod 34480343)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1326167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1326167, 1)] : List FactorBlock).map factorBlockValue).prod) = 34480343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_1326167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34480343) ^ 17240171 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34480343) ^ 2652334 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34480343) ^ 26 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_39081611 : Nat.Prime 39081611 := by
  apply lucas_primality 39081611 (2 : ZMod 39081611)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (199, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (199, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 39081611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_199
      · exact prime_fiftyNineBE_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39081611) ^ 19540805 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 39081611) ^ 7816322 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 39081611) ^ 953210 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 39081611) ^ 196390 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 39081611) ^ 81590 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_42909089 : Nat.Prime 42909089 := by
  apply lucas_primality 42909089 (3 : ZMod 42909089)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (78877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (78877, 1)] : List FactorBlock).map factorBlockValue).prod) = 42909089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_78877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42909089) ^ 21454544 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 42909089) ^ 2524064 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 42909089) ^ 544 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_43462487 : Nat.Prime 43462487 := by
  apply lucas_primality 43462487 (5 : ZMod 43462487)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21731243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21731243, 1)] : List FactorBlock).map factorBlockValue).prod) = 43462487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_21731243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 43462487) ^ 21731243 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43462487) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_43697651 : Nat.Prime 43697651 := by
  apply lucas_primality 43697651 (6 : ZMod 43697651)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (101, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (101, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 43697651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_101
      · exact prime_fiftyNineBE_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 43697651) ^ 21848825 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43697651) ^ 8739530 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43697651) ^ 2570450 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43697651) ^ 432650 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43697651) ^ 85850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_49160569 : Nat.Prime 49160569 := by
  apply lucas_primality 49160569 (11 : ZMod 49160569)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (29, 1), (37, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (29, 1), (37, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 49160569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49160569) ^ 24580284 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49160569) ^ 16386856 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49160569) ^ 2137416 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49160569) ^ 1695192 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49160569) ^ 1328664 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49160569) ^ 592296 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_52151069 : Nat.Prime 52151069 := by
  apply lucas_primality 52151069 (2 : ZMod 52151069)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13037767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13037767, 1)] : List FactorBlock).map factorBlockValue).prod) = 52151069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_13037767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 52151069) ^ 26075534 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 52151069) ^ 4 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_52715543 : Nat.Prime 52715543 := by
  apply lucas_primality 52715543 (5 : ZMod 52715543)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (283, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (283, 1), (8467, 1)] : List FactorBlock).map factorBlockValue).prod) = 52715543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_283
      · exact prime_fiftyNineBE_8467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52715543) ^ 26357771 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 52715543) ^ 4792322 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 52715543) ^ 186274 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 52715543) ^ 6226 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_54469091 : Nat.Prime 54469091 := by
  apply lucas_primality 54469091 (2 : ZMod 54469091)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (418993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (418993, 1)] : List FactorBlock).map factorBlockValue).prod) = 54469091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_418993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54469091) ^ 27234545 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54469091) ^ 10893818 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54469091) ^ 4189930 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 54469091) ^ 130 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_58085981 : Nat.Prime 58085981 := by
  apply lucas_primality 58085981 (2 : ZMod 58085981)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2904299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2904299, 1)] : List FactorBlock).map factorBlockValue).prod) = 58085981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_2904299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58085981) ^ 29042990 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58085981) ^ 11617196 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58085981) ^ 20 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_60958883 : Nat.Prime 60958883 := by
  apply lucas_primality 60958883 (2 : ZMod 60958883)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (743401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (743401, 1)] : List FactorBlock).map factorBlockValue).prod) = 60958883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_743401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60958883) ^ 30479441 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 60958883) ^ 1486802 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 60958883) ^ 82 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_65566049 : Nat.Prime 65566049 := by
  apply lucas_primality 65566049 (3 : ZMod 65566049)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2048939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2048939, 1)] : List FactorBlock).map factorBlockValue).prod) = 65566049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_2048939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 65566049) ^ 32783024 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 65566049) ^ 32 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_68830379 : Nat.Prime 68830379 := by
  apply lucas_primality 68830379 (2 : ZMod 68830379)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34415189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34415189, 1)] : List FactorBlock).map factorBlockValue).prod) = 68830379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_34415189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 68830379) ^ 34415189 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68830379) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_71807977 : Nat.Prime 71807977 := by
  apply lucas_primality 71807977 (5 : ZMod 71807977)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (997333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (997333, 1)] : List FactorBlock).map factorBlockValue).prod) = 71807977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_997333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 71807977) ^ 35903988 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 71807977) ^ 23935992 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 71807977) ^ 72 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_73710751 : Nat.Prime 73710751 := by
  apply lucas_primality 73710751 (3 : ZMod 73710751)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (29, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (29, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) = 73710751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_3389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73710751) ^ 36855375 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73710751) ^ 24570250 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73710751) ^ 14742150 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73710751) ^ 2541750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73710751) ^ 21750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_75742963 : Nat.Prime 75742963 := by
  apply lucas_primality 75742963 (2 : ZMod 75742963)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2089, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2089, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod) = 75742963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_2089
      · exact prime_fiftyNineBE_6043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75742963) ^ 37871481 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75742963) ^ 25247654 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75742963) ^ 36258 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75742963) ^ 12534 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_86885129 : Nat.Prime 86885129 := by
  apply lucas_primality 86885129 (3 : ZMod 86885129)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (373, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (373, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 86885129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_373
      · exact prime_fiftyNineBE_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86885129) ^ 43442564 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86885129) ^ 7898648 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86885129) ^ 232936 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 86885129) ^ 32824 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_87395303 : Nat.Prime 87395303 := by
  apply lucas_primality 87395303 (5 : ZMod 87395303)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43697651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43697651, 1)] : List FactorBlock).map factorBlockValue).prod) = 87395303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_43697651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 87395303) ^ 43697651 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 87395303) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_106693141 : Nat.Prime 106693141 := by
  apply lucas_primality 106693141 (18 : ZMod 106693141)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1778219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1778219, 1)] : List FactorBlock).map factorBlockValue).prod) = 106693141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_1778219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (18 : ZMod 106693141) ^ 53346570 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (18 : ZMod 106693141) ^ 35564380 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (18 : ZMod 106693141) ^ 21338628 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (18 : ZMod 106693141) ^ 60 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_114073579 : Nat.Prime 114073579 := by
  apply lucas_primality 114073579 (2 : ZMod 114073579)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2237, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2237, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 114073579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_2237
      · exact prime_fiftyNineBE_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 114073579) ^ 57036789 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 114073579) ^ 38024526 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 114073579) ^ 50994 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 114073579) ^ 40266 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_116171963 : Nat.Prime 116171963 := by
  apply lucas_primality 116171963 (2 : ZMod 116171963)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (58085981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (58085981, 1)] : List FactorBlock).map factorBlockValue).prod) = 116171963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_58085981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 116171963) ^ 58085981 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 116171963) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_119281663 : Nat.Prime 119281663 := by
  apply lucas_primality 119281663 (3 : ZMod 119281663)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (179, 1), (37021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (179, 1), (37021, 1)] : List FactorBlock).map factorBlockValue).prod) = 119281663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_179
      · exact prime_fiftyNineBE_37021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119281663) ^ 59640831 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281663) ^ 39760554 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281663) ^ 666378 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281663) ^ 3222 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_119857373 : Nat.Prime 119857373 := by
  apply lucas_primality 119857373 (2 : ZMod 119857373)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (71, 1), (6299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (71, 1), (6299, 1)] : List FactorBlock).map factorBlockValue).prod) = 119857373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_67
      · exact prime_fiftyNineBE_71
      · exact prime_fiftyNineBE_6299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119857373) ^ 59928686 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119857373) ^ 1788916 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119857373) ^ 1688132 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119857373) ^ 19028 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_122796529 : Nat.Prime 122796529 := by
  apply lucas_primality 122796529 (26 : ZMod 122796529)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67, 1), (38183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67, 1), (38183, 1)] : List FactorBlock).map factorBlockValue).prod) = 122796529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_67
      · exact prime_fiftyNineBE_38183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 122796529) ^ 61398264 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 122796529) ^ 40932176 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 122796529) ^ 1832784 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 122796529) ^ 3216 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_125202499 : Nat.Prime 125202499 := by
  apply lucas_primality 125202499 (2 : ZMod 125202499)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (67, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (67, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) = 125202499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_67
      · exact prime_fiftyNineBE_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125202499) ^ 62601249 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125202499) ^ 41734166 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125202499) ^ 2911686 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125202499) ^ 1868694 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125202499) ^ 17286 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_132243847 : Nat.Prime 132243847 := by
  apply lucas_primality 132243847 (3 : ZMod 132243847)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (37, 1), (12157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (37, 1), (12157, 1)] : List FactorBlock).map factorBlockValue).prod) = 132243847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_12157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 132243847) ^ 66121923 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 132243847) ^ 44081282 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 132243847) ^ 18891978 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 132243847) ^ 3574158 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 132243847) ^ 10878 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_147200611 : Nat.Prime 147200611 := by
  apply lucas_primality 147200611 (2 : ZMod 147200611)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (53, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (53, 1), (2153, 1)] : List FactorBlock).map factorBlockValue).prod) = 147200611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_53
      · exact prime_fiftyNineBE_2153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147200611) ^ 73600305 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 147200611) ^ 49066870 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 147200611) ^ 29440122 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 147200611) ^ 3423270 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 147200611) ^ 2777370 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 147200611) ^ 68370 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_153530929 : Nat.Prime 153530929 := by
  apply lucas_primality 153530929 (11 : ZMod 153530929)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (157, 1), (6791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (157, 1), (6791, 1)] : List FactorBlock).map factorBlockValue).prod) = 153530929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_157
      · exact prime_fiftyNineBE_6791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 153530929) ^ 76765464 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 153530929) ^ 51176976 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 153530929) ^ 977904 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 153530929) ^ 22608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_174790607 : Nat.Prime 174790607 := by
  apply lucas_primality 174790607 (5 : ZMod 174790607)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (87395303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (87395303, 1)] : List FactorBlock).map factorBlockValue).prod) = 174790607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_87395303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 174790607) ^ 87395303 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 174790607) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_192116063 : Nat.Prime 192116063 := by
  apply lucas_primality 192116063 (5 : ZMod 192116063)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (2596163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (2596163, 1)] : List FactorBlock).map factorBlockValue).prod) = 192116063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_2596163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 192116063) ^ 96058031 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 192116063) ^ 5192326 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 192116063) ^ 74 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_234489667 : Nat.Prime 234489667 := by
  apply lucas_primality 234489667 (2 : ZMod 234489667)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39081611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39081611, 1)] : List FactorBlock).map factorBlockValue).prod) = 234489667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_39081611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 234489667) ^ 117244833 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 234489667) ^ 78163222 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 234489667) ^ 6 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_273536453 : Nat.Prime 273536453 := by
  apply lucas_primality 273536453 (2 : ZMod 273536453)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (9769159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (9769159, 1)] : List FactorBlock).map factorBlockValue).prod) = 273536453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_9769159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 273536453) ^ 136768226 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 273536453) ^ 39076636 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 273536453) ^ 28 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_316835609 : Nat.Prime 316835609 := by
  apply lucas_primality 316835609 (3 : ZMod 316835609)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (239, 1), (165709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (239, 1), (165709, 1)] : List FactorBlock).map factorBlockValue).prod) = 316835609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_239
      · exact prime_fiftyNineBE_165709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 316835609) ^ 158417804 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 316835609) ^ 1325672 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 316835609) ^ 1912 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_333430841 : Nat.Prime 333430841 := by
  apply lucas_primality 333430841 (6 : ZMod 333430841)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (8335771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (8335771, 1)] : List FactorBlock).map factorBlockValue).prod) = 333430841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_8335771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 333430841) ^ 166715420 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 333430841) ^ 66686168 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 333430841) ^ 40 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_350453183 : Nat.Prime 350453183 := by
  apply lucas_primality 350453183 (5 : ZMod 350453183)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (151, 1), (26987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (151, 1), (26987, 1)] : List FactorBlock).map factorBlockValue).prod) = 350453183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_151
      · exact prime_fiftyNineBE_26987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 350453183) ^ 175226591 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 350453183) ^ 8150074 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 350453183) ^ 2320882 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 350453183) ^ 12986 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_369871511 : Nat.Prime 369871511 := by
  apply lucas_primality 369871511 (7 : ZMod 369871511)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 2), (29, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 2), (29, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 369871511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 369871511) ^ 184935755 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 369871511) ^ 73974302 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 369871511) ^ 16081370 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 369871511) ^ 12754190 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 369871511) ^ 153410 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_370099277 : Nat.Prime 370099277 := by
  apply lucas_primality 370099277 (2 : ZMod 370099277)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (863, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (863, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 370099277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_863
      · exact prime_fiftyNineBE_3697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 370099277) ^ 185049638 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 370099277) ^ 12762044 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 370099277) ^ 428852 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 370099277) ^ 100108 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_420358487 : Nat.Prime 420358487 := by
  apply lucas_primality 420358487 (5 : ZMod 420358487)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (5126323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (5126323, 1)] : List FactorBlock).map factorBlockValue).prod) = 420358487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_5126323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 420358487) ^ 210179243 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 420358487) ^ 10252646 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 420358487) ^ 82 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_447066107 : Nat.Prime 447066107 := by
  apply lucas_primality 447066107 (2 : ZMod 447066107)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11953, 1), (18701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11953, 1), (18701, 1)] : List FactorBlock).map factorBlockValue).prod) = 447066107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11953
      · exact prime_fiftyNineBE_18701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 447066107) ^ 223533053 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 447066107) ^ 37402 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 447066107) ^ 23906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_454457779 : Nat.Prime 454457779 := by
  apply lucas_primality 454457779 (14 : ZMod 454457779)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (75742963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (75742963, 1)] : List FactorBlock).map factorBlockValue).prod) = 454457779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_75742963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 454457779) ^ 227228889 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 454457779) ^ 151485926 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 454457779) ^ 6 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_476370493 : Nat.Prime 476370493 := by
  apply lucas_primality 476370493 (2 : ZMod 476370493)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (97, 1), (31481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (97, 1), (31481, 1)] : List FactorBlock).map factorBlockValue).prod) = 476370493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_97
      · exact prime_fiftyNineBE_31481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 476370493) ^ 238185246 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 476370493) ^ 158790164 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 476370493) ^ 36643884 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 476370493) ^ 4911036 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 476370493) ^ 15132 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_486591359 : Nat.Prime 486591359 := by
  apply lucas_primality 486591359 (13 : ZMod 486591359)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (961643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (961643, 1)] : List FactorBlock).map factorBlockValue).prod) = 486591359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_961643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 486591359) ^ 243295679 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 486591359) ^ 44235578 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 486591359) ^ 21156146 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 486591359) ^ 506 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_486750041 : Nat.Prime 486750041 := by
  apply lucas_primality 486750041 (3 : ZMod 486750041)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (137, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (137, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) = 486750041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_137
      · exact prime_fiftyNineBE_12689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 486750041) ^ 243375020 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486750041) ^ 97350008 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486750041) ^ 69535720 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486750041) ^ 3552920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486750041) ^ 38360 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_526041757 : Nat.Prime 526041757 := by
  apply lucas_primality 526041757 (2 : ZMod 526041757)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1777, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1777, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 526041757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1777
      · exact prime_fiftyNineBE_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 526041757) ^ 263020878 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 526041757) ^ 175347252 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 526041757) ^ 296028 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 526041757) ^ 191916 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_547336159 : Nat.Prime 547336159 := by
  apply lucas_primality 547336159 (3 : ZMod 547336159)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3677, 1), (24809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3677, 1), (24809, 1)] : List FactorBlock).map factorBlockValue).prod) = 547336159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_3677
      · exact prime_fiftyNineBE_24809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 547336159) ^ 273668079 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 547336159) ^ 182445386 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 547336159) ^ 148854 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 547336159) ^ 22062 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_550643033 : Nat.Prime 550643033 := by
  apply lucas_primality 550643033 (3 : ZMod 550643033)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (68830379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (68830379, 1)] : List FactorBlock).map factorBlockValue).prod) = 550643033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_68830379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 550643033) ^ 275321516 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 550643033) ^ 8 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_666861683 : Nat.Prime 666861683 := by
  apply lucas_primality 666861683 (2 : ZMod 666861683)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (333430841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (333430841, 1)] : List FactorBlock).map factorBlockValue).prod) = 666861683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_333430841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 666861683) ^ 333430841 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 666861683) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_693747121 : Nat.Prime 693747121 := by
  apply lucas_primality 693747121 (26 : ZMod 693747121)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (262783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (262783, 1)] : List FactorBlock).map factorBlockValue).prod) = 693747121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_262783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 693747121) ^ 346873560 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 693747121) ^ 231249040 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 693747121) ^ 138749424 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 693747121) ^ 63067920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 693747121) ^ 2640 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_806935609 : Nat.Prime 806935609 := by
  apply lucas_primality 806935609 (11 : ZMod 806935609)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (653, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (653, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) = 806935609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_653
      · exact prime_fiftyNineBE_1907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 806935609) ^ 403467804 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 806935609) ^ 268978536 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 806935609) ^ 1235736 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 806935609) ^ 423144 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_842285623 : Nat.Prime 842285623 := by
  apply lucas_primality 842285623 (3 : ZMod 842285623)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (6103519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (6103519, 1)] : List FactorBlock).map factorBlockValue).prod) = 842285623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_6103519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 842285623) ^ 421142811 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 842285623) ^ 280761874 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 842285623) ^ 36621114 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 842285623) ^ 138 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_973500083 : Nat.Prime 973500083 := by
  apply lucas_primality 973500083 (2 : ZMod 973500083)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (486750041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (486750041, 1)] : List FactorBlock).map factorBlockValue).prod) = 973500083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_486750041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 973500083) ^ 486750041 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 973500083) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1199799443 : Nat.Prime 1199799443 := by
  apply lucas_primality 1199799443 (2 : ZMod 1199799443)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (641, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (641, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199799443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_283
      · exact prime_fiftyNineBE_641
      · exact prime_fiftyNineBE_3307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1199799443) ^ 599899721 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199799443) ^ 4239574 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199799443) ^ 1871762 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199799443) ^ 362806 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1272371701 : Nat.Prime 1272371701 := by
  apply lucas_primality 1272371701 (6 : ZMod 1272371701)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (4241239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (4241239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1272371701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_4241239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1272371701) ^ 636185850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1272371701) ^ 424123900 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1272371701) ^ 254474340 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1272371701) ^ 300 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1278867683 : Nat.Prime 1278867683 := by
  apply lucas_primality 1278867683 (2 : ZMod 1278867683)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (3922907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (3922907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1278867683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_163
      · exact prime_fiftyNineBE_3922907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1278867683) ^ 639433841 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278867683) ^ 7845814 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278867683) ^ 326 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1315544183 : Nat.Prime 1315544183 := by
  apply lucas_primality 1315544183 (5 : ZMod 1315544183)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (131, 1), (63559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (131, 1), (63559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1315544183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_79
      · exact prime_fiftyNineBE_131
      · exact prime_fiftyNineBE_63559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1315544183) ^ 657772091 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1315544183) ^ 16652458 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1315544183) ^ 10042322 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1315544183) ^ 20698 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1480728127 : Nat.Prime 1480728127 := by
  apply lucas_primality 1480728127 (3 : ZMod 1480728127)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (349, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (349, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1480728127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_79
      · exact prime_fiftyNineBE_349
      · exact prime_fiftyNineBE_8951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1480728127) ^ 740364063 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480728127) ^ 493576042 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480728127) ^ 18743394 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480728127) ^ 4242774 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480728127) ^ 165426 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1575565247 : Nat.Prime 1575565247 := by
  apply lucas_primality 1575565247 (5 : ZMod 1575565247)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (1754527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (1754527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1575565247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_449
      · exact prime_fiftyNineBE_1754527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1575565247) ^ 787782623 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1575565247) ^ 3509054 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1575565247) ^ 898 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1581466291 : Nat.Prime 1581466291 := by
  apply lucas_primality 1581466291 (3 : ZMod 1581466291)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (52715543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (52715543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581466291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_52715543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1581466291) ^ 790733145 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581466291) ^ 527155430 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581466291) ^ 316293258 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1581466291) ^ 30 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1787963953 : Nat.Prime 1787963953 := by
  apply lucas_primality 1787963953 (7 : ZMod 1787963953)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (163, 1), (228523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (163, 1), (228523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1787963953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_163
      · exact prime_fiftyNineBE_228523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1787963953) ^ 893981976 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1787963953) ^ 595987984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1787963953) ^ 10969104 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1787963953) ^ 7824 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1923137809 : Nat.Prime 1923137809 := by
  apply lucas_primality 1923137809 (19 : ZMod 1923137809)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (71, 1), (564301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (71, 1), (564301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1923137809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_71
      · exact prime_fiftyNineBE_564301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 1923137809) ^ 961568904 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1923137809) ^ 641045936 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1923137809) ^ 27086448 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1923137809) ^ 3408 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1955352439 : Nat.Prime 1955352439 := by
  apply lucas_primality 1955352439 (12 : ZMod 1955352439)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (61, 1), (136987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (61, 1), (136987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1955352439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_61
      · exact prime_fiftyNineBE_136987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1955352439) ^ 977676219 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (12 : ZMod 1955352439) ^ 651784146 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (12 : ZMod 1955352439) ^ 150411726 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (12 : ZMod 1955352439) ^ 32054958 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (12 : ZMod 1955352439) ^ 14274 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1956292103 : Nat.Prime 1956292103 := by
  apply lucas_primality 1956292103 (5 : ZMod 1956292103)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (449, 1), (128147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (449, 1), (128147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1956292103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_449
      · exact prime_fiftyNineBE_128147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1956292103) ^ 978146051 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1956292103) ^ 115076006 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1956292103) ^ 4356998 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1956292103) ^ 15266 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2437226251 : Nat.Prime 2437226251 := by
  apply lucas_primality 2437226251 (3 : ZMod 2437226251)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (17, 1), (38231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (17, 1), (38231, 1)] : List FactorBlock).map factorBlockValue).prod) = 2437226251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_38231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2437226251) ^ 1218613125 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437226251) ^ 812408750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437226251) ^ 487445250 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437226251) ^ 143366250 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2437226251) ^ 63750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2646694909 : Nat.Prime 2646694909 := by
  apply lucas_primality 2646694909 (2 : ZMod 2646694909)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (13, 1), (19, 1), (27059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (13, 1), (19, 1), (27059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2646694909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_27059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2646694909) ^ 1323347454 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2646694909) ^ 882231636 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2646694909) ^ 240608628 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2646694909) ^ 203591916 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2646694909) ^ 139299732 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2646694909) ^ 97812 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2858222959 : Nat.Prime 2858222959 := by
  apply lucas_primality 2858222959 (3 : ZMod 2858222959)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (476370493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (476370493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858222959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_476370493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2858222959) ^ 1429111479 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858222959) ^ 952740986 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858222959) ^ 6 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2867092663 : Nat.Prime 2867092663 := by
  apply lucas_primality 2867092663 (3 : ZMod 2867092663)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4547, 1), (15013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4547, 1), (15013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2867092663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_4547
      · exact prime_fiftyNineBE_15013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2867092663) ^ 1433546331 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867092663) ^ 955697554 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867092663) ^ 409584666 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867092663) ^ 630546 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867092663) ^ 190974 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3756454561 : Nat.Prime 3756454561 := by
  apply lucas_primality 3756454561 (7 : ZMod 3756454561)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (2608649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (2608649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3756454561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_2608649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3756454561) ^ 1878227280 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756454561) ^ 1252151520 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756454561) ^ 751290912 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3756454561) ^ 1440 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3826647229 : Nat.Prime 3826647229 := by
  apply lucas_primality 3826647229 (13 : ZMod 3826647229)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (1031, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (1031, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) = 3826647229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_1031
      · exact prime_fiftyNineBE_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3826647229) ^ 1913323614 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3826647229) ^ 1275549076 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3826647229) ^ 88991796 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3826647229) ^ 3711588 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 3826647229) ^ 531996 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3967315411 : Nat.Prime 3967315411 := by
  apply lucas_primality 3967315411 (2 : ZMod 3967315411)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (132243847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (132243847, 1)] : List FactorBlock).map factorBlockValue).prod) = 3967315411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_132243847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3967315411) ^ 1983657705 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3967315411) ^ 1322438470 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3967315411) ^ 793463082 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3967315411) ^ 30 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4186876123 : Nat.Prime 4186876123 := by
  apply lucas_primality 4186876123 (3 : ZMod 4186876123)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 3), (13, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 3), (13, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) = 4186876123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_4481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4186876123) ^ 2093438061 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4186876123) ^ 1395625374 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4186876123) ^ 380625102 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4186876123) ^ 322067394 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4186876123) ^ 934362 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4284377137 : Nat.Prime 4284377137 := by
  apply lucas_primality 4284377137 (7 : ZMod 4284377137)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 2), (176051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 2), (176051, 1)] : List FactorBlock).map factorBlockValue).prod) = 4284377137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_176051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4284377137) ^ 2142188568 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4284377137) ^ 1428125712 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4284377137) ^ 329567472 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4284377137) ^ 24336 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4330203961 : Nat.Prime 4330203961 := by
  apply lucas_primality 4330203961 (7 : ZMod 4330203961)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (2122649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (2122649, 1)] : List FactorBlock).map factorBlockValue).prod) = 4330203961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_2122649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4330203961) ^ 2165101980 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4330203961) ^ 1443401320 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4330203961) ^ 866040792 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4330203961) ^ 254717880 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4330203961) ^ 2040 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4881076483 : Nat.Prime 4881076483 := by
  apply lucas_primality 4881076483 (2 : ZMod 4881076483)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (37, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (37, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) = 4881076483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_76079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4881076483) ^ 2440538241 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4881076483) ^ 1627025494 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4881076483) ^ 287122146 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4881076483) ^ 131920986 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4881076483) ^ 64158 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5120546173 : Nat.Prime 5120546173 := by
  apply lucas_primality 5120546173 (2 : ZMod 5120546173)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (60958883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (60958883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5120546173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_60958883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5120546173) ^ 2560273086 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5120546173) ^ 1706848724 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5120546173) ^ 731506596 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5120546173) ^ 84 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5155103011 : Nat.Prime 5155103011 := by
  apply lucas_primality 5155103011 (2 : ZMod 5155103011)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7541, 1), (22787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7541, 1), (22787, 1)] : List FactorBlock).map factorBlockValue).prod) = 5155103011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7541
      · exact prime_fiftyNineBE_22787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5155103011) ^ 2577551505 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155103011) ^ 1718367670 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155103011) ^ 1031020602 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155103011) ^ 683610 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155103011) ^ 226230 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5666647729 : Nat.Prime 5666647729 := by
  apply lucas_primality 5666647729 (11 : ZMod 5666647729)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (31, 1), (77719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (31, 1), (77719, 1)] : List FactorBlock).map factorBlockValue).prod) = 5666647729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_77719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5666647729) ^ 2833323864 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5666647729) ^ 1888882576 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5666647729) ^ 809521104 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5666647729) ^ 182795088 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5666647729) ^ 72912 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5819234579 : Nat.Prime 5819234579 := by
  apply lucas_primality 5819234579 (2 : ZMod 5819234579)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (22210819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (22210819, 1)] : List FactorBlock).map factorBlockValue).prod) = 5819234579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_131
      · exact prime_fiftyNineBE_22210819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5819234579) ^ 2909617289 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5819234579) ^ 44421638 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5819234579) ^ 262 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5841000499 : Nat.Prime 5841000499 := by
  apply lucas_primality 5841000499 (10 : ZMod 5841000499)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (973500083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (973500083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5841000499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_973500083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5841000499) ^ 2920500249 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 5841000499) ^ 1947000166 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 5841000499) ^ 6 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_6249954071 : Nat.Prime 6249954071 := by
  apply lucas_primality 6249954071 (7 : ZMod 6249954071)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (269, 1), (2323403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (269, 1), (2323403, 1)] : List FactorBlock).map factorBlockValue).prod) = 6249954071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_269
      · exact prime_fiftyNineBE_2323403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6249954071) ^ 3124977035 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6249954071) ^ 1249990814 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6249954071) ^ 23234030 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6249954071) ^ 2690 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_6327594893 : Nat.Prime 6327594893 := by
  apply lucas_primality 6327594893 (2 : ZMod 6327594893)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1091, 1), (1449953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1091, 1), (1449953, 1)] : List FactorBlock).map factorBlockValue).prod) = 6327594893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_1091
      · exact prime_fiftyNineBE_1449953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6327594893) ^ 3163797446 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6327594893) ^ 5799812 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6327594893) ^ 4364 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_6631012567 : Nat.Prime 6631012567 := by
  apply lucas_primality 6631012567 (5 : ZMod 6631012567)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (122796529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (122796529, 1)] : List FactorBlock).map factorBlockValue).prod) = 6631012567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_122796529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6631012567) ^ 3315506283 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6631012567) ^ 2210337522 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6631012567) ^ 54 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_7470189509 : Nat.Prime 7470189509 := by
  apply lucas_primality 7470189509 (2 : ZMod 7470189509)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (389, 1), (4800893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (389, 1), (4800893, 1)] : List FactorBlock).map factorBlockValue).prod) = 7470189509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_389
      · exact prime_fiftyNineBE_4800893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7470189509) ^ 3735094754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7470189509) ^ 19203572 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7470189509) ^ 1556 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_8833119349 : Nat.Prime 8833119349 := by
  apply lucas_primality 8833119349 (6 : ZMod 8833119349)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (8270711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (8270711, 1)] : List FactorBlock).map factorBlockValue).prod) = 8833119349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_89
      · exact prime_fiftyNineBE_8270711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 8833119349) ^ 4416559674 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 8833119349) ^ 2944373116 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 8833119349) ^ 99248532 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 8833119349) ^ 1068 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_8983999393 : Nat.Prime 8983999393 := by
  apply lucas_primality 8983999393 (10 : ZMod 8983999393)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (31, 1), (821, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (31, 1), (821, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) = 8983999393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_821
      · exact prime_fiftyNineBE_3677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8983999393) ^ 4491999696 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8983999393) ^ 2994666464 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8983999393) ^ 289806432 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8983999393) ^ 10942752 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8983999393) ^ 2443296 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_9267619147 : Nat.Prime 9267619147 := by
  apply lucas_primality 9267619147 (3 : ZMod 9267619147)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (83, 1), (641713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (83, 1), (641713, 1)] : List FactorBlock).map factorBlockValue).prod) = 9267619147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_83
      · exact prime_fiftyNineBE_641713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9267619147) ^ 4633809573 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9267619147) ^ 3089206382 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9267619147) ^ 319573074 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9267619147) ^ 111658062 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9267619147) ^ 14442 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_9422502709 : Nat.Prime 9422502709 := by
  apply lucas_primality 9422502709 (6 : ZMod 9422502709)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (389, 1), (2018531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (389, 1), (2018531, 1)] : List FactorBlock).map factorBlockValue).prod) = 9422502709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_389
      · exact prime_fiftyNineBE_2018531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9422502709) ^ 4711251354 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9422502709) ^ 3140834236 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9422502709) ^ 24222372 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9422502709) ^ 4668 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_10106570347 : Nat.Prime 10106570347 := by
  apply lucas_primality 10106570347 (3 : ZMod 10106570347)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (4308001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (4308001, 1)] : List FactorBlock).map factorBlockValue).prod) = 10106570347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_4308001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10106570347) ^ 5053285173 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10106570347) ^ 3368856782 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10106570347) ^ 594504138 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10106570347) ^ 439416102 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10106570347) ^ 2346 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_10120594633 : Nat.Prime 10120594633 := by
  apply lucas_primality 10120594633 (11 : ZMod 10120594633)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (24805379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (24805379, 1)] : List FactorBlock).map factorBlockValue).prod) = 10120594633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_24805379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 10120594633) ^ 5060297316 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 10120594633) ^ 3373531544 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 10120594633) ^ 595329096 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 10120594633) ^ 408 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11432891837 : Nat.Prime 11432891837 := by
  apply lucas_primality 11432891837 (2 : ZMod 11432891837)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2858222959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2858222959, 1)] : List FactorBlock).map factorBlockValue).prod) = 11432891837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_2858222959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11432891837) ^ 5716445918 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11432891837) ^ 4 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11945270863 : Nat.Prime 11945270863 := by
  apply lucas_primality 11945270863 (3 : ZMod 11945270863)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (59, 1), (229549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (59, 1), (229549, 1)] : List FactorBlock).map factorBlockValue).prod) = 11945270863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_59
      · exact prime_fiftyNineBE_229549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11945270863) ^ 5972635431 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11945270863) ^ 3981756954 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11945270863) ^ 1706467266 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11945270863) ^ 202462218 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11945270863) ^ 52038 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11991786269 : Nat.Prime 11991786269 := by
  apply lucas_primality 11991786269 (2 : ZMod 11991786269)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (11, 1), (794579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (11, 1), (794579, 1)] : List FactorBlock).map factorBlockValue).prod) = 11991786269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_794579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11991786269) ^ 5995893134 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11991786269) ^ 1713112324 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11991786269) ^ 1090162388 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11991786269) ^ 15092 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_12257855413 : Nat.Prime 12257855413 := by
  apply lucas_primality 12257855413 (6 : ZMod 12257855413)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (293, 1), (316937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (293, 1), (316937, 1)] : List FactorBlock).map factorBlockValue).prod) = 12257855413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_293
      · exact prime_fiftyNineBE_316937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12257855413) ^ 6128927706 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 12257855413) ^ 4085951804 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 12257855413) ^ 1114350492 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 12257855413) ^ 41835684 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 12257855413) ^ 38676 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_12563545523 : Nat.Prime 12563545523 := by
  apply lucas_primality 12563545523 (2 : ZMod 12563545523)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (31, 1), (969559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (31, 1), (969559, 1)] : List FactorBlock).map factorBlockValue).prod) = 12563545523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_969559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12563545523) ^ 6281772761 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12563545523) ^ 1142140502 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12563545523) ^ 661239238 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12563545523) ^ 405275662 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12563545523) ^ 12958 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_14853086021 : Nat.Prime 14853086021 := by
  apply lucas_primality 14853086021 (2 : ZMod 14853086021)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 2), (883061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 2), (883061, 1)] : List FactorBlock).map factorBlockValue).prod) = 14853086021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_883061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14853086021) ^ 7426543010 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853086021) ^ 2970617204 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853086021) ^ 512175380 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853086021) ^ 16820 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_14940379019 : Nat.Prime 14940379019 := by
  apply lucas_primality 14940379019 (2 : ZMod 14940379019)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7470189509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7470189509, 1)] : List FactorBlock).map factorBlockValue).prod) = 14940379019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7470189509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14940379019) ^ 7470189509 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940379019) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_15110162567 : Nat.Prime 15110162567 := by
  apply lucas_primality 15110162567 (5 : ZMod 15110162567)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (127, 1), (164789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (127, 1), (164789, 1)] : List FactorBlock).map factorBlockValue).prod) = 15110162567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_127
      · exact prime_fiftyNineBE_164789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15110162567) ^ 7555081283 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15110162567) ^ 795271714 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15110162567) ^ 118977658 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15110162567) ^ 91694 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_15447272041 : Nat.Prime 15447272041 := by
  apply lucas_primality 15447272041 (31 : ZMod 15447272041)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (42909089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (42909089, 1)] : List FactorBlock).map factorBlockValue).prod) = 15447272041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_42909089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 15447272041) ^ 7723636020 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (31 : ZMod 15447272041) ^ 5149090680 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (31 : ZMod 15447272041) ^ 3089454408 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (31 : ZMod 15447272041) ^ 360 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_15984218527 : Nat.Prime 15984218527 := by
  apply lucas_primality 15984218527 (5 : ZMod 15984218527)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (27464293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (27464293, 1)] : List FactorBlock).map factorBlockValue).prod) = 15984218527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_97
      · exact prime_fiftyNineBE_27464293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15984218527) ^ 7992109263 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15984218527) ^ 5328072842 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15984218527) ^ 164785758 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 15984218527) ^ 582 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_17276229119 : Nat.Prime 17276229119 := by
  apply lucas_primality 17276229119 (7 : ZMod 17276229119)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (283, 1), (126653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (283, 1), (126653, 1)] : List FactorBlock).map factorBlockValue).prod) = 17276229119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_241
      · exact prime_fiftyNineBE_283
      · exact prime_fiftyNineBE_126653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17276229119) ^ 8638114559 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17276229119) ^ 71685598 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17276229119) ^ 61046746 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17276229119) ^ 136406 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_17620577057 : Nat.Prime 17620577057 := by
  apply lucas_primality 17620577057 (3 : ZMod 17620577057)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (550643033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (550643033, 1)] : List FactorBlock).map factorBlockValue).prod) = 17620577057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_550643033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 17620577057) ^ 8810288528 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17620577057) ^ 32 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_22892996023 : Nat.Prime 22892996023 := by
  apply lucas_primality 22892996023 (3 : ZMod 22892996023)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (9511, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (9511, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) = 22892996023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_9511
      · exact prime_fiftyNineBE_30859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22892996023) ^ 11446498011 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22892996023) ^ 7630998674 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22892996023) ^ 1760999694 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22892996023) ^ 2407002 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22892996023) ^ 741858 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_25127091047 : Nat.Prime 25127091047 := by
  apply lucas_primality 25127091047 (5 : ZMod 25127091047)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12563545523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12563545523, 1)] : List FactorBlock).map factorBlockValue).prod) = 25127091047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_12563545523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 25127091047) ^ 12563545523 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 25127091047) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_25421823013 : Nat.Prime 25421823013 := by
  apply lucas_primality 25421823013 (2 : ZMod 25421823013)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (263, 1), (101963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (263, 1), (101963, 1)] : List FactorBlock).map factorBlockValue).prod) = 25421823013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_79
      · exact prime_fiftyNineBE_263
      · exact prime_fiftyNineBE_101963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25421823013) ^ 12710911506 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421823013) ^ 8473941004 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421823013) ^ 321795228 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421823013) ^ 96660924 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421823013) ^ 249324 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_25573867183 : Nat.Prime 25573867183 := by
  apply lucas_primality 25573867183 (3 : ZMod 25573867183)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (211, 1), (2244503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (211, 1), (2244503, 1)] : List FactorBlock).map factorBlockValue).prod) = 25573867183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_211
      · exact prime_fiftyNineBE_2244503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25573867183) ^ 12786933591 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25573867183) ^ 8524622394 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25573867183) ^ 121203162 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25573867183) ^ 11394 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_29114934413 : Nat.Prime 29114934413 := by
  apply lucas_primality 29114934413 (2 : ZMod 29114934413)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (223, 1), (431, 1), (75731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (223, 1), (431, 1), (75731, 1)] : List FactorBlock).map factorBlockValue).prod) = 29114934413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_223
      · exact prime_fiftyNineBE_431
      · exact prime_fiftyNineBE_75731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29114934413) ^ 14557467206 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114934413) ^ 130560244 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114934413) ^ 67552052 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29114934413) ^ 384452 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_30128403307 : Nat.Prime 30128403307 := by
  apply lucas_primality 30128403307 (2 : ZMod 30128403307)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (157, 1), (43753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (157, 1), (43753, 1)] : List FactorBlock).map factorBlockValue).prod) = 30128403307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_157
      · exact prime_fiftyNineBE_43753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30128403307) ^ 15064201653 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30128403307) ^ 10042801102 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30128403307) ^ 1772259018 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30128403307) ^ 700660542 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30128403307) ^ 191900658 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30128403307) ^ 688602 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_30756108923 : Nat.Prime 30756108923 := by
  apply lucas_primality 30756108923 (2 : ZMod 30756108923)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (127, 1), (1572559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (127, 1), (1572559, 1)] : List FactorBlock).map factorBlockValue).prod) = 30756108923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_127
      · exact prime_fiftyNineBE_1572559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30756108923) ^ 15378054461 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30756108923) ^ 4393729846 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30756108923) ^ 2796009902 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30756108923) ^ 242174086 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30756108923) ^ 19558 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_37447050383 : Nat.Prime 37447050383 := by
  apply lucas_primality 37447050383 (5 : ZMod 37447050383)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (1571, 1), (34747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (1571, 1), (34747, 1)] : List FactorBlock).map factorBlockValue).prod) = 37447050383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_1571
      · exact prime_fiftyNineBE_34747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37447050383) ^ 18723525191 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 37447050383) ^ 5349578626 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 37447050383) ^ 23836442 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 37447050383) ^ 1077706 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_41127807101 : Nat.Prime 41127807101 := by
  apply lucas_primality 41127807101 (2 : ZMod 41127807101)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (2287, 1), (179833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (2287, 1), (179833, 1)] : List FactorBlock).map factorBlockValue).prod) = 41127807101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_2287
      · exact prime_fiftyNineBE_179833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41127807101) ^ 20563903550 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41127807101) ^ 8225561420 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41127807101) ^ 17983300 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41127807101) ^ 228700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_41460387557 : Nat.Prime 41460387557 := by
  apply lucas_primality 41460387557 (2 : ZMod 41460387557)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1480728127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1480728127, 1)] : List FactorBlock).map factorBlockValue).prod) = 41460387557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_1480728127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41460387557) ^ 20730193778 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41460387557) ^ 5922912508 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41460387557) ^ 28 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_42015855967 : Nat.Prime 42015855967 := by
  apply lucas_primality 42015855967 (7 : ZMod 42015855967)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29063, 1), (34421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29063, 1), (34421, 1)] : List FactorBlock).map factorBlockValue).prod) = 42015855967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_29063
      · exact prime_fiftyNineBE_34421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42015855967) ^ 21007927983 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42015855967) ^ 14005285322 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42015855967) ^ 6002265138 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42015855967) ^ 1445682 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42015855967) ^ 1220646 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_43876210783 : Nat.Prime 43876210783 := by
  apply lucas_primality 43876210783 (6 : ZMod 43876210783)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1571, 1), (4654807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1571, 1), (4654807, 1)] : List FactorBlock).map factorBlockValue).prod) = 43876210783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1571
      · exact prime_fiftyNineBE_4654807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 43876210783) ^ 21938105391 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43876210783) ^ 14625403594 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43876210783) ^ 27928842 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 43876210783) ^ 9426 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_45555790487 : Nat.Prime 45555790487 := by
  apply lucas_primality 45555790487 (5 : ZMod 45555790487)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1051, 1), (461119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1051, 1), (461119, 1)] : List FactorBlock).map factorBlockValue).prod) = 45555790487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_47
      · exact prime_fiftyNineBE_1051
      · exact prime_fiftyNineBE_461119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45555790487) ^ 22777895243 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 45555790487) ^ 969272138 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 45555790487) ^ 43345186 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 45555790487) ^ 98794 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_56666477291 : Nat.Prime 56666477291 := by
  apply lucas_primality 56666477291 (2 : ZMod 56666477291)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5666647729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5666647729, 1)] : List FactorBlock).map factorBlockValue).prod) = 56666477291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_5666647729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56666477291) ^ 28333238645 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 56666477291) ^ 11333295458 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 56666477291) ^ 10 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_62601347297 : Nat.Prime 62601347297 := by
  apply lucas_primality 62601347297 (3 : ZMod 62601347297)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1956292103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1956292103, 1)] : List FactorBlock).map factorBlockValue).prod) = 62601347297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_1956292103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62601347297) ^ 31300673648 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 62601347297) ^ 32 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_77100717217 : Nat.Prime 77100717217 := by
  apply lucas_primality 77100717217 (5 : ZMod 77100717217)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (37, 1), (113, 1), (192091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (37, 1), (113, 1), (192091, 1)] : List FactorBlock).map factorBlockValue).prod) = 77100717217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_113
      · exact prime_fiftyNineBE_192091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77100717217) ^ 38550358608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 77100717217) ^ 25700239072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 77100717217) ^ 2083803168 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 77100717217) ^ 682307232 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 77100717217) ^ 401376 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_81023614531 : Nat.Prime 81023614531 := by
  apply lucas_primality 81023614531 (3 : ZMod 81023614531)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1019, 1), (2650429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1019, 1), (2650429, 1)] : List FactorBlock).map factorBlockValue).prod) = 81023614531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_1019
      · exact prime_fiftyNineBE_2650429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81023614531) ^ 40511807265 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81023614531) ^ 27007871510 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81023614531) ^ 16204722906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81023614531) ^ 79512870 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81023614531) ^ 30570 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_120513613229 : Nat.Prime 120513613229 := by
  apply lucas_primality 120513613229 (2 : ZMod 120513613229)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30128403307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30128403307, 1)] : List FactorBlock).map factorBlockValue).prod) = 120513613229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_30128403307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 120513613229) ^ 60256806614 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 120513613229) ^ 4 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_120843805969 : Nat.Prime 120843805969 := by
  apply lucas_primality 120843805969 (11 : ZMod 120843805969)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (29, 1), (28937693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (29, 1), (28937693, 1)] : List FactorBlock).map factorBlockValue).prod) = 120843805969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_28937693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 120843805969) ^ 60421902984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 120843805969) ^ 40281268656 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 120843805969) ^ 4167027792 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 120843805969) ^ 4176 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_123967369849 : Nat.Prime 123967369849 := by
  apply lucas_primality 123967369849 (13 : ZMod 123967369849)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (4003, 1), (184337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (4003, 1), (184337, 1)] : List FactorBlock).map factorBlockValue).prod) = 123967369849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_4003
      · exact prime_fiftyNineBE_184337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 123967369849) ^ 61983684924 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 123967369849) ^ 41322456616 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 123967369849) ^ 17709624264 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 123967369849) ^ 30968616 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 123967369849) ^ 672504 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_125299858253 : Nat.Prime 125299858253 := by
  apply lucas_primality 125299858253 (2 : ZMod 125299858253)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (97, 1), (829, 1), (16937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (97, 1), (829, 1), (16937, 1)] : List FactorBlock).map factorBlockValue).prod) = 125299858253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_97
      · exact prime_fiftyNineBE_829
      · exact prime_fiftyNineBE_16937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125299858253) ^ 62649929126 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125299858253) ^ 5447819924 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125299858253) ^ 1291751116 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125299858253) ^ 151145788 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125299858253) ^ 7397996 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_140406795967 : Nat.Prime 140406795967 := by
  apply lucas_primality 140406795967 (3 : ZMod 140406795967)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (806935609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (806935609, 1)] : List FactorBlock).map factorBlockValue).prod) = 140406795967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_806935609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 140406795967) ^ 70203397983 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 140406795967) ^ 46802265322 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 140406795967) ^ 4841613654 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 140406795967) ^ 174 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_184961117717 : Nat.Prime 184961117717 := by
  apply lucas_primality 184961117717 (2 : ZMod 184961117717)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (353, 1), (2099, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (353, 1), (2099, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) = 184961117717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_353
      · exact prime_fiftyNineBE_2099
      · exact prime_fiftyNineBE_3671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184961117717) ^ 92480558858 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 184961117717) ^ 10880065748 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 184961117717) ^ 523969172 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 184961117717) ^ 88118684 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 184961117717) ^ 50384396 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_187635624931 : Nat.Prime 187635624931 := by
  apply lucas_primality 187635624931 (3 : ZMod 187635624931)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 2), (53, 1), (77587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 2), (53, 1), (77587, 1)] : List FactorBlock).map factorBlockValue).prod) = 187635624931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_53
      · exact prime_fiftyNineBE_77587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 187635624931) ^ 93817812465 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187635624931) ^ 62545208310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187635624931) ^ 37527124986 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187635624931) ^ 14433509610 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187635624931) ^ 3540294810 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187635624931) ^ 2418390 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_190562033449 : Nat.Prime 190562033449 := by
  apply lucas_primality 190562033449 (11 : ZMod 190562033449)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2646694909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2646694909, 1)] : List FactorBlock).map factorBlockValue).prod) = 190562033449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_2646694909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 190562033449) ^ 95281016724 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 190562033449) ^ 63520677816 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 190562033449) ^ 72 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_191169433409 : Nat.Prime 191169433409 := by
  apply lucas_primality 191169433409 (3 : ZMod 191169433409)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (23, 1), (1097, 1), (118387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (23, 1), (1097, 1), (118387, 1)] : List FactorBlock).map factorBlockValue).prod) = 191169433409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_1097
      · exact prime_fiftyNineBE_118387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 191169433409) ^ 95584716704 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 191169433409) ^ 8311714496 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 191169433409) ^ 174265664 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 191169433409) ^ 1614784 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_262966319813 : Nat.Prime 262966319813 := by
  apply lucas_primality 262966319813 (3 : ZMod 262966319813)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (59, 1), (2347, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (59, 1), (2347, 1), (9689, 1)] : List FactorBlock).map factorBlockValue).prod) = 262966319813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_59
      · exact prime_fiftyNineBE_2347
      · exact prime_fiftyNineBE_9689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 262966319813) ^ 131483159906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 262966319813) ^ 37566617116 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 262966319813) ^ 4457056268 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 262966319813) ^ 112043596 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 262966319813) ^ 27140708 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_278708155969 : Nat.Prime 278708155969 := by
  apply lucas_primality 278708155969 (14 : ZMod 278708155969)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (37, 1), (239, 1), (14923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (37, 1), (239, 1), (14923, 1)] : List FactorBlock).map factorBlockValue).prod) = 278708155969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_239
      · exact prime_fiftyNineBE_14923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 278708155969) ^ 139354077984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 278708155969) ^ 92902718656 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 278708155969) ^ 25337105088 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 278708155969) ^ 7532652864 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 278708155969) ^ 1166142912 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 278708155969) ^ 18676416 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_303372272867 : Nat.Prime 303372272867 := by
  apply lucas_primality 303372272867 (2 : ZMod 303372272867)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37, 1), (2903, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37, 1), (2903, 1), (108631, 1)] : List FactorBlock).map factorBlockValue).prod) = 303372272867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_2903
      · exact prime_fiftyNineBE_108631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 303372272867) ^ 151686136433 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 303372272867) ^ 23336328682 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 303372272867) ^ 8199250618 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 303372272867) ^ 104503022 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 303372272867) ^ 2792686 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_314158636567 : Nat.Prime 314158636567 := by
  apply lucas_primality 314158636567 (5 : ZMod 314158636567)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (17, 1), (114073579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (17, 1), (114073579, 1)] : List FactorBlock).map factorBlockValue).prod) = 314158636567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_114073579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 314158636567) ^ 157079318283 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 314158636567) ^ 104719545522 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 314158636567) ^ 18479919798 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 314158636567) ^ 2754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_321933811079 : Nat.Prime 321933811079 := by
  apply lucas_primality 321933811079 (11 : ZMod 321933811079)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (65809, 1), (222361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (65809, 1), (222361, 1)] : List FactorBlock).map factorBlockValue).prod) = 321933811079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_65809
      · exact prime_fiftyNineBE_222361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 321933811079) ^ 160966905539 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 321933811079) ^ 29266710098 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 321933811079) ^ 4891942 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 321933811079) ^ 1447798 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_372830483089 : Nat.Prime 372830483089 := by
  apply lucas_primality 372830483089 (17 : ZMod 372830483089)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (369871511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (369871511, 1)] : List FactorBlock).map factorBlockValue).prod) = 372830483089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_369871511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 372830483089) ^ 186415241544 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 372830483089) ^ 124276827696 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 372830483089) ^ 53261497584 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 372830483089) ^ 1008 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_381505575331 : Nat.Prime 381505575331 := by
  apply lucas_primality 381505575331 (3 : ZMod 381505575331)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (293, 1), (311, 1), (4229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (293, 1), (311, 1), (4229, 1)] : List FactorBlock).map factorBlockValue).prod) = 381505575331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_293
      · exact prime_fiftyNineBE_311
      · exact prime_fiftyNineBE_4229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 381505575331) ^ 190752787665 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 127168525110 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 76301115066 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 34682325030 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 1302066810 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 1226706030 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 381505575331) ^ 90211770 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_435968829971 : Nat.Prime 435968829971 := by
  apply lucas_primality 435968829971 (2 : ZMod 435968829971)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (271, 1), (499, 1), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (271, 1), (499, 1), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) = 435968829971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_271
      · exact prime_fiftyNineBE_499
      · exact prime_fiftyNineBE_11117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435968829971) ^ 217984414985 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 435968829971) ^ 87193765994 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 435968829971) ^ 15033407930 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 435968829971) ^ 1608741070 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 435968829971) ^ 873685030 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 435968829971) ^ 39216410 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_568872639221 : Nat.Prime 568872639221 := by
  apply lucas_primality 568872639221 (2 : ZMod 568872639221)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (693747121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (693747121, 1)] : List FactorBlock).map factorBlockValue).prod) = 568872639221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_693747121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 568872639221) ^ 284436319610 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 568872639221) ^ 113774527844 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 568872639221) ^ 13874942420 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 568872639221) ^ 820 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_597159887237 : Nat.Prime 597159887237 := by
  apply lucas_primality 597159887237 (2 : ZMod 597159887237)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (113, 1), (167, 1), (719189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (113, 1), (167, 1), (719189, 1)] : List FactorBlock).map factorBlockValue).prod) = 597159887237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_113
      · exact prime_fiftyNineBE_167
      · exact prime_fiftyNineBE_719189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 597159887237) ^ 298579943618 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 597159887237) ^ 54287262476 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 597159887237) ^ 5284600772 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 597159887237) ^ 3575807708 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 597159887237) ^ 830324 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_716149357237 : Nat.Prime 716149357237 := by
  apply lucas_primality 716149357237 (2 : ZMod 716149357237)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (6631012567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (6631012567, 1)] : List FactorBlock).map factorBlockValue).prod) = 716149357237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_6631012567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 716149357237) ^ 358074678618 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 716149357237) ^ 238716452412 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 716149357237) ^ 108 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_725287803217 : Nat.Prime 725287803217 := by
  apply lucas_primality 725287803217 (5 : ZMod 725287803217)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (15110162567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (15110162567, 1)] : List FactorBlock).map factorBlockValue).prod) = 725287803217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_15110162567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 725287803217) ^ 362643901608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 725287803217) ^ 241762601072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 725287803217) ^ 48 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_756645276601 : Nat.Prime 756645276601 := by
  apply lucas_primality 756645276601 (13 : ZMod 756645276601)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (420358487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (420358487, 1)] : List FactorBlock).map factorBlockValue).prod) = 756645276601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_420358487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 756645276601) ^ 378322638300 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 756645276601) ^ 252215092200 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 756645276601) ^ 151329055320 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 756645276601) ^ 1800 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1992704839751 : Nat.Prime 1992704839751 := by
  apply lucas_primality 1992704839751 (26 : ZMod 1992704839751)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (17, 1), (10613, 1), (44179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (17, 1), (10613, 1), (44179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1992704839751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_10613
      · exact prime_fiftyNineBE_44179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1992704839751) ^ 996352419875 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 1992704839751) ^ 398540967950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 1992704839751) ^ 117217931750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 1992704839751) ^ 187760750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (26 : ZMod 1992704839751) ^ 45105250 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2123867609783 : Nat.Prime 2123867609783 := by
  apply lucas_primality 2123867609783 (10 : ZMod 2123867609783)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (25747, 1), (36793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (25747, 1), (36793, 1)] : List FactorBlock).map factorBlockValue).prod) = 2123867609783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_59
      · exact prime_fiftyNineBE_25747
      · exact prime_fiftyNineBE_36793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2123867609783) ^ 1061933804891 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2123867609783) ^ 111782505778 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2123867609783) ^ 35997756098 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2123867609783) ^ 82489906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2123867609783) ^ 57724774 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2669508558217 : Nat.Prime 2669508558217 := by
  apply lucas_primality 2669508558217 (5 : ZMod 2669508558217)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (503, 1), (73710751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (503, 1), (73710751, 1)] : List FactorBlock).map factorBlockValue).prod) = 2669508558217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_503
      · exact prime_fiftyNineBE_73710751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2669508558217) ^ 1334754279108 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669508558217) ^ 889836186072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669508558217) ^ 5307174072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669508558217) ^ 36216 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2770143604777 : Nat.Prime 2770143604777 := by
  apply lucas_primality 2770143604777 (10 : ZMod 2770143604777)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (107, 1), (119857373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (107, 1), (119857373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2770143604777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_107
      · exact prime_fiftyNineBE_119857373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2770143604777) ^ 1385071802388 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2770143604777) ^ 923381201592 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2770143604777) ^ 25889192568 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2770143604777) ^ 23112 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3274172194889 : Nat.Prime 3274172194889 := by
  apply lucas_primality 3274172194889 (3 : ZMod 3274172194889)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (43, 1), (113, 1), (1718971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (43, 1), (113, 1), (1718971, 1)] : List FactorBlock).map factorBlockValue).prod) = 3274172194889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_113
      · exact prime_fiftyNineBE_1718971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3274172194889) ^ 1637086097444 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3274172194889) ^ 467738884984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3274172194889) ^ 76143539416 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3274172194889) ^ 28974975176 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3274172194889) ^ 1904728 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3377983771769 : Nat.Prime 3377983771769 := by
  apply lucas_primality 3377983771769 (3 : ZMod 3377983771769)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (8983999393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (8983999393, 1)] : List FactorBlock).map factorBlockValue).prod) = 3377983771769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_47
      · exact prime_fiftyNineBE_8983999393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3377983771769) ^ 1688991885884 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377983771769) ^ 71871995144 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377983771769) ^ 376 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3917146406627 : Nat.Prime 3917146406627 := by
  apply lucas_primality 3917146406627 (2 : ZMod 3917146406627)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73673, 1), (26584681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73673, 1), (26584681, 1)] : List FactorBlock).map factorBlockValue).prod) = 3917146406627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_73673
      · exact prime_fiftyNineBE_26584681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3917146406627) ^ 1958573203313 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3917146406627) ^ 53169362 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3917146406627) ^ 147346 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4457267112703 : Nat.Prime 4457267112703 := by
  apply lucas_primality 4457267112703 (3 : ZMod 4457267112703)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (17276229119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (17276229119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4457267112703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_17276229119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4457267112703) ^ 2228633556351 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4457267112703) ^ 1485755704234 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4457267112703) ^ 103657374714 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4457267112703) ^ 258 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4543338724453 : Nat.Prime 4543338724453 := by
  apply lucas_primality 4543338724453 (2 : ZMod 4543338724453)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (31, 1), (370099277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (31, 1), (370099277, 1)] : List FactorBlock).map factorBlockValue).prod) = 4543338724453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_370099277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4543338724453) ^ 2271669362226 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4543338724453) ^ 1514446241484 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4543338724453) ^ 413030793132 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4543338724453) ^ 146559313692 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4543338724453) ^ 12276 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4738447939879 : Nat.Prime 4738447939879 := by
  apply lucas_primality 4738447939879 (3 : ZMod 4738447939879)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (1663, 1), (3368011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (1663, 1), (3368011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4738447939879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_47
      · exact prime_fiftyNineBE_1663
      · exact prime_fiftyNineBE_3368011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4738447939879) ^ 2369223969939 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4738447939879) ^ 1579482646626 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4738447939879) ^ 100818041274 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4738447939879) ^ 2849337306 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4738447939879) ^ 1406898 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5129232786389 : Nat.Prime 5129232786389 := by
  apply lucas_primality 5129232786389 (2 : ZMod 5129232786389)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3659, 1), (350453183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3659, 1), (350453183, 1)] : List FactorBlock).map factorBlockValue).prod) = 5129232786389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3659
      · exact prime_fiftyNineBE_350453183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5129232786389) ^ 2564616393194 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5129232786389) ^ 1401812732 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5129232786389) ^ 14636 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_7047621928183 : Nat.Prime 7047621928183 := by
  apply lucas_primality 7047621928183 (3 : ZMod 7047621928183)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (89, 1), (1199799443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (89, 1), (1199799443, 1)] : List FactorBlock).map factorBlockValue).prod) = 7047621928183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_89
      · exact prime_fiftyNineBE_1199799443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7047621928183) ^ 3523810964091 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7047621928183) ^ 2349207309394 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7047621928183) ^ 640692902562 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7047621928183) ^ 79186763238 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7047621928183) ^ 5874 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_7460811921859 : Nat.Prime 7460811921859 := by
  apply lucas_primality 7460811921859 (2 : ZMod 7460811921859)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1613, 1), (24867881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1613, 1), (24867881, 1)] : List FactorBlock).map factorBlockValue).prod) = 7460811921859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_1613
      · exact prime_fiftyNineBE_24867881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7460811921859) ^ 3730405960929 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7460811921859) ^ 2486937307286 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7460811921859) ^ 240671352318 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7460811921859) ^ 4625425866 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7460811921859) ^ 300018 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_7918528778093 : Nat.Prime 7918528778093 := by
  apply lucas_primality 7918528778093 (3 : ZMod 7918528778093)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (146291, 1), (796009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (146291, 1), (796009, 1)] : List FactorBlock).map factorBlockValue).prod) = 7918528778093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_146291
      · exact prime_fiftyNineBE_796009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7918528778093) ^ 3959264389046 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7918528778093) ^ 465795810476 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7918528778093) ^ 54128612 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7918528778093) ^ 9947788 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_8074225653191 : Nat.Prime 8074225653191 := by
  apply lucas_primality 8074225653191 (11 : ZMod 8074225653191)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211, 1), (3826647229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211, 1), (3826647229, 1)] : List FactorBlock).map factorBlockValue).prod) = 8074225653191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_211
      · exact prime_fiftyNineBE_3826647229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 8074225653191) ^ 4037112826595 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8074225653191) ^ 1614845130638 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8074225653191) ^ 38266472290 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8074225653191) ^ 2110 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_8459066417831 : Nat.Prime 8459066417831 := by
  apply lucas_primality 8459066417831 (7 : ZMod 8459066417831)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (120843805969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (120843805969, 1)] : List FactorBlock).map factorBlockValue).prod) = 8459066417831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_120843805969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8459066417831) ^ 4229533208915 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8459066417831) ^ 1691813283566 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8459066417831) ^ 1208438059690 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8459066417831) ^ 70 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_10188775071443 : Nat.Prime 10188775071443 := by
  apply lucas_primality 10188775071443 (5 : ZMod 10188775071443)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (157, 1), (8609, 1), (342647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (157, 1), (8609, 1), (342647, 1)] : List FactorBlock).map factorBlockValue).prod) = 10188775071443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_157
      · exact prime_fiftyNineBE_8609
      · exact prime_fiftyNineBE_342647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10188775071443) ^ 5094387535721 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10188775071443) ^ 926252279222 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10188775071443) ^ 64896656506 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10188775071443) ^ 1183502738 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10188775071443) ^ 29735486 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_10751301340537 : Nat.Prime 10751301340537 := by
  apply lucas_primality 10751301340537 (5 : ZMod 10751301340537)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (15447272041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (15447272041, 1)] : List FactorBlock).map factorBlockValue).prod) = 10751301340537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_15447272041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10751301340537) ^ 5375650670268 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10751301340537) ^ 3583767113512 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10751301340537) ^ 370734528984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10751301340537) ^ 696 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11108919226913 : Nat.Prime 11108919226913 := by
  apply lucas_primality 11108919226913 (3 : ZMod 11108919226913)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (139, 1), (192116063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (139, 1), (192116063, 1)] : List FactorBlock).map factorBlockValue).prod) = 11108919226913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_139
      · exact prime_fiftyNineBE_192116063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11108919226913) ^ 5554459613456 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11108919226913) ^ 854532248224 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11108919226913) ^ 79920282208 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11108919226913) ^ 57824 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11505161919931 : Nat.Prime 11505161919931 := by
  apply lucas_primality 11505161919931 (7 : ZMod 11505161919931)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (7219, 1), (7589207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (7219, 1), (7589207, 1)] : List FactorBlock).map factorBlockValue).prod) = 11505161919931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_7219
      · exact prime_fiftyNineBE_7589207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11505161919931) ^ 5752580959965 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 11505161919931) ^ 3835053973310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 11505161919931) ^ 2301032383986 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 11505161919931) ^ 1643594559990 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 11505161919931) ^ 1593733470 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 11505161919931) ^ 1515990 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_14414127095339 : Nat.Prime 14414127095339 := by
  apply lucas_primality 14414127095339 (2 : ZMod 14414127095339)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (11991786269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (11991786269, 1)] : List FactorBlock).map factorBlockValue).prod) = 14414127095339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_601
      · exact prime_fiftyNineBE_11991786269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14414127095339) ^ 7207063547669 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14414127095339) ^ 23983572538 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14414127095339) ^ 1202 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_14925739520521 : Nat.Prime 14925739520521 := by
  apply lucas_primality 14925739520521 (17 : ZMod 14925739520521)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (41460387557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (41460387557, 1)] : List FactorBlock).map factorBlockValue).prod) = 14925739520521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_41460387557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 14925739520521) ^ 7462869760260 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 14925739520521) ^ 4975246506840 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 14925739520521) ^ 2985147904104 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 14925739520521) ^ 360 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_15721923094681 : Nat.Prime 15721923094681 := by
  apply lucas_primality 15721923094681 (14 : ZMod 15721923094681)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (487, 1), (128047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (487, 1), (128047, 1)] : List FactorBlock).map factorBlockValue).prod) = 15721923094681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_191
      · exact prime_fiftyNineBE_487
      · exact prime_fiftyNineBE_128047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15721923094681) ^ 7860961547340 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 5240641031560 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 3144384618936 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 1429265735880 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 82313733480 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 32283209640 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 15721923094681) ^ 122782440 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_17249724290923 : Nat.Prime 17249724290923 := by
  apply lucas_primality 17249724290923 (2 : ZMod 17249724290923)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (4881076483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (4881076483, 1)] : List FactorBlock).map factorBlockValue).prod) = 17249724290923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_4881076483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17249724290923) ^ 8624862145461 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17249724290923) ^ 5749908096974 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17249724290923) ^ 907880225838 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17249724290923) ^ 556442719062 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17249724290923) ^ 3534 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_20051435568449 : Nat.Prime 20051435568449 := by
  apply lucas_primality 20051435568449 (3 : ZMod 20051435568449)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (31, 1), (10106570347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (31, 1), (10106570347, 1)] : List FactorBlock).map factorBlockValue).prod) = 20051435568449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_10106570347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20051435568449) ^ 10025717784224 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 20051435568449) ^ 646820502208 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 20051435568449) ^ 1984 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_22217838453827 : Nat.Prime 22217838453827 := by
  apply lucas_primality 22217838453827 (2 : ZMod 22217838453827)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11108919226913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11108919226913, 1)] : List FactorBlock).map factorBlockValue).prod) = 22217838453827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11108919226913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22217838453827) ^ 11108919226913 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22217838453827) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_23171065185137 : Nat.Prime 23171065185137 := by
  apply lucas_primality 23171065185137 (3 : ZMod 23171065185137)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (67, 1), (89, 1), (3607, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (67, 1), (89, 1), (3607, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 23171065185137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_67
      · exact prime_fiftyNineBE_89
      · exact prime_fiftyNineBE_3607
      · exact prime_fiftyNineBE_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23171065185137) ^ 11585532592568 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23171065185137) ^ 2106460471376 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23171065185137) ^ 345836793808 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23171065185137) ^ 260349047024 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23171065185137) ^ 6423916048 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23171065185137) ^ 3785503216 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_23642088741307 : Nat.Prime 23642088741307 := by
  apply lucas_primality 23642088741307 (2 : ZMod 23642088741307)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (187635624931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (187635624931, 1)] : List FactorBlock).map factorBlockValue).prod) = 23642088741307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_187635624931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23642088741307) ^ 11821044370653 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23642088741307) ^ 7880696247102 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23642088741307) ^ 3377441248758 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23642088741307) ^ 126 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_32117686496551 : Nat.Prime 32117686496551 := by
  apply lucas_primality 32117686496551 (15 : ZMod 32117686496551)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (3756454561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (3756454561, 1)] : List FactorBlock).map factorBlockValue).prod) = 32117686496551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_3756454561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32117686496551) ^ 16058843248275 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (15 : ZMod 32117686496551) ^ 10705895498850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (15 : ZMod 32117686496551) ^ 6423537299310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (15 : ZMod 32117686496551) ^ 1690404552450 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (15 : ZMod 32117686496551) ^ 8550 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_35019882965839 : Nat.Prime 35019882965839 := by
  apply lucas_primality 35019882965839 (3 : ZMod 35019882965839)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (56666477291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (56666477291, 1)] : List FactorBlock).map factorBlockValue).prod) = 35019882965839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_103
      · exact prime_fiftyNineBE_56666477291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35019882965839) ^ 17509941482919 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35019882965839) ^ 11673294321946 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35019882965839) ^ 339998863746 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 35019882965839) ^ 618 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_46211291799683 : Nat.Prime 46211291799683 := by
  apply lucas_primality 46211291799683 (2 : ZMod 46211291799683)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5393, 1), (4284377137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5393, 1), (4284377137, 1)] : List FactorBlock).map factorBlockValue).prod) = 46211291799683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5393
      · exact prime_fiftyNineBE_4284377137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46211291799683) ^ 23105645899841 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46211291799683) ^ 8568754274 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46211291799683) ^ 10786 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_58935099508003 : Nat.Prime 58935099508003 := by
  apply lucas_primality 58935099508003 (2 : ZMod 58935099508003)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3274172194889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3274172194889, 1)] : List FactorBlock).map factorBlockValue).prod) = 58935099508003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_3274172194889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58935099508003) ^ 29467549754001 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58935099508003) ^ 19645033169334 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58935099508003) ^ 18 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_62752653409801 : Nat.Prime 62752653409801 := by
  apply lucas_primality 62752653409801 (17 : ZMod 62752653409801)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (139, 1), (2269, 1), (331613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (139, 1), (2269, 1), (331613, 1)] : List FactorBlock).map factorBlockValue).prod) = 62752653409801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_139
      · exact prime_fiftyNineBE_2269
      · exact prime_fiftyNineBE_331613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 62752653409801) ^ 31376326704900 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 62752653409801) ^ 20917551136600 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 62752653409801) ^ 12550530681960 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 62752653409801) ^ 451457938200 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 62752653409801) ^ 27656524200 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 62752653409801) ^ 189234600 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_79842531641359 : Nat.Prime 79842531641359 := by
  apply lucas_primality 79842531641359 (13 : ZMod 79842531641359)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (6547, 1), (65566049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (6547, 1), (65566049, 1)] : List FactorBlock).map factorBlockValue).prod) = 79842531641359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_6547
      · exact prime_fiftyNineBE_65566049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 79842531641359) ^ 39921265820679 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 79842531641359) ^ 26614177213786 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 79842531641359) ^ 2575565536818 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 79842531641359) ^ 12195285114 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 79842531641359) ^ 1217742 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_111570632864101 : Nat.Prime 111570632864101 := by
  apply lucas_primality 111570632864101 (6 : ZMod 111570632864101)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (123967369849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (123967369849, 1)] : List FactorBlock).map factorBlockValue).prod) = 111570632864101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_123967369849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 111570632864101) ^ 55785316432050 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 111570632864101) ^ 37190210954700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 111570632864101) ^ 22314126572820 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 111570632864101) ^ 900 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_130886152536877 : Nat.Prime 130886152536877 := by
  apply lucas_primality 130886152536877 (2 : ZMod 130886152536877)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (131, 1), (443, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (131, 1), (443, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) = 130886152536877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_131
      · exact prime_fiftyNineBE_443
      · exact prime_fiftyNineBE_32299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130886152536877) ^ 65443076268438 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 43628717512292 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 11898741139716 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 5690702284212 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 999130935396 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 295454068932 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 130886152536877) ^ 4052328324 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_158124579894791 : Nat.Prime 158124579894791 := by
  apply lucas_primality 158124579894791 (11 : ZMod 158124579894791)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (198659, 1), (2744689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (198659, 1), (2744689, 1)] : List FactorBlock).map factorBlockValue).prod) = 158124579894791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_198659
      · exact prime_fiftyNineBE_2744689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 158124579894791) ^ 79062289947395 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 158124579894791) ^ 31624915978958 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 158124579894791) ^ 5452571720510 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 158124579894791) ^ 795959810 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 158124579894791) ^ 57611110 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_186865599075191 : Nat.Prime 186865599075191 := by
  apply lucas_primality 186865599075191 (11 : ZMod 186865599075191)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2669508558217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2669508558217, 1)] : List FactorBlock).map factorBlockValue).prod) = 186865599075191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_2669508558217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 186865599075191) ^ 93432799537595 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 186865599075191) ^ 37373119815038 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 186865599075191) ^ 26695085582170 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 186865599075191) ^ 70 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_187072223729401 : Nat.Prime 187072223729401 := by
  apply lucas_primality 187072223729401 (7 : ZMod 187072223729401)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (181, 1), (821, 1), (699383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (181, 1), (821, 1), (699383, 1)] : List FactorBlock).map factorBlockValue).prod) = 187072223729401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_181
      · exact prime_fiftyNineBE_821
      · exact prime_fiftyNineBE_699383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 187072223729401) ^ 93536111864700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 187072223729401) ^ 62357407909800 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 187072223729401) ^ 37414444745880 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 187072223729401) ^ 1033548197400 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 187072223729401) ^ 227858981400 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 187072223729401) ^ 267481800 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_220612989573419 : Nat.Prime 220612989573419 := by
  apply lucas_primality 220612989573419 (2 : ZMod 220612989573419)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37, 1), (13421, 1), (17087209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37, 1), (13421, 1), (17087209, 1)] : List FactorBlock).map factorBlockValue).prod) = 220612989573419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_37
      · exact prime_fiftyNineBE_13421
      · exact prime_fiftyNineBE_17087209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 220612989573419) ^ 110306494786709 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220612989573419) ^ 16970229967186 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220612989573419) ^ 5962513231714 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220612989573419) ^ 16437895058 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220612989573419) ^ 12911002 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_248957664447083 : Nat.Prime 248957664447083 := by
  apply lucas_primality 248957664447083 (2 : ZMod 248957664447083)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (673, 1), (184961117717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (673, 1), (184961117717, 1)] : List FactorBlock).map factorBlockValue).prod) = 248957664447083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_673
      · exact prime_fiftyNineBE_184961117717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 248957664447083) ^ 124478832223541 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 248957664447083) ^ 369922235434 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 248957664447083) ^ 1346 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_316249159789583 : Nat.Prime 316249159789583 := by
  apply lucas_primality 316249159789583 (5 : ZMod 316249159789583)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (158124579894791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (158124579894791, 1)] : List FactorBlock).map factorBlockValue).prod) = 316249159789583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_158124579894791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 316249159789583) ^ 158124579894791 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 316249159789583) ^ 2 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_329999972019199 : Nat.Prime 329999972019199 := by
  apply lucas_primality 329999972019199 (3 : ZMod 329999972019199)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (311, 1), (313, 1), (43462487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (311, 1), (313, 1), (43462487, 1)] : List FactorBlock).map factorBlockValue).prod) = 329999972019199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_311
      · exact prime_fiftyNineBE_313
      · exact prime_fiftyNineBE_43462487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 329999972019199) ^ 164999986009599 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 329999972019199) ^ 109999990673066 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 329999972019199) ^ 25384613232246 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 329999972019199) ^ 1061093157618 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 329999972019199) ^ 1054313009646 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 329999972019199) ^ 7592754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_436820731558151 : Nat.Prime 436820731558151 := by
  apply lucas_primality 436820731558151 (19 : ZMod 436820731558151)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (59, 1), (523, 1), (3673, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (59, 1), (523, 1), (3673, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) = 436820731558151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_59
      · exact prime_fiftyNineBE_523
      · exact prime_fiftyNineBE_3673
      · exact prime_fiftyNineBE_4057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 436820731558151) ^ 218410365779075 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 87364146311630 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 22990564818850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 7403741212850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 835221284050 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 118927506550 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (19 : ZMod 436820731558151) ^ 107670872950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_451831288860319 : Nat.Prime 451831288860319 := by
  apply lucas_primality 451831288860319 (3 : ZMod 451831288860319)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (601, 1), (125299858253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (601, 1), (125299858253, 1)] : List FactorBlock).map factorBlockValue).prod) = 451831288860319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_601
      · exact prime_fiftyNineBE_125299858253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 451831288860319) ^ 225915644430159 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 451831288860319) ^ 150610429620106 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 451831288860319) ^ 751799149518 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 451831288860319) ^ 3606 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_803428899812863 : Nat.Prime 803428899812863 := by
  apply lucas_primality 803428899812863 (5 : ZMod 803428899812863)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (7047621928183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (7047621928183, 1)] : List FactorBlock).map factorBlockValue).prod) = 803428899812863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_7047621928183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 803428899812863) ^ 401714449906431 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428899812863) ^ 267809633270954 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428899812863) ^ 42285731569098 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 803428899812863) ^ 114 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1324160865384611 : Nat.Prime 1324160865384611 := by
  apply lucas_primality 1324160865384611 (2 : ZMod 1324160865384611)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (31, 1), (137, 1), (1231, 1), (2302543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (31, 1), (137, 1), (1231, 1), (2302543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1324160865384611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_31
      · exact prime_fiftyNineBE_137
      · exact prime_fiftyNineBE_1231
      · exact prime_fiftyNineBE_2302543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1324160865384611) ^ 662080432692305 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 264832173076922 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 120378260489510 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 42714866625310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 9665407776530 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 1075679013310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1324160865384611) ^ 575086270 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1535124523077253 : Nat.Prime 1535124523077253 := by
  apply lucas_primality 1535124523077253 (7 : ZMod 1535124523077253)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (17, 1), (278708155969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (17, 1), (278708155969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1535124523077253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_278708155969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1535124523077253) ^ 767562261538626 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1535124523077253) ^ 511708174359084 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1535124523077253) ^ 90301442533956 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1535124523077253) ^ 5508 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1706071365737113 : Nat.Prime 1706071365737113 := by
  apply lucas_primality 1706071365737113 (5 : ZMod 1706071365737113)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (541, 1), (11945270863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (541, 1), (11945270863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706071365737113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_541
      · exact prime_fiftyNineBE_11945270863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1706071365737113) ^ 853035682868556 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1706071365737113) ^ 568690455245704 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1706071365737113) ^ 155097396885192 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1706071365737113) ^ 3153551507832 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1706071365737113) ^ 142824 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1801185000486467 : Nat.Prime 1801185000486467 := by
  apply lucas_primality 1801185000486467 (2 : ZMod 1801185000486467)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (32429, 1), (3967315411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (32429, 1), (3967315411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801185000486467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_32429
      · exact prime_fiftyNineBE_3967315411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1801185000486467) ^ 900592500243233 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801185000486467) ^ 257312142926638 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801185000486467) ^ 55542415754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801185000486467) ^ 454006 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1958634202977497 : Nat.Prime 1958634202977497 := by
  apply lucas_primality 1958634202977497 (3 : ZMod 1958634202977497)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (83, 1), (198533, 1), (1350703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (83, 1), (198533, 1), (1350703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1958634202977497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_83
      · exact prime_fiftyNineBE_198533
      · exact prime_fiftyNineBE_1350703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1958634202977497) ^ 979317101488748 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958634202977497) ^ 178057654816136 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958634202977497) ^ 23598002445512 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958634202977497) ^ 9865534712 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958634202977497) ^ 1450085032 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2023599269167163 : Nat.Prime 2023599269167163 := by
  apply lucas_primality 2023599269167163 (2 : ZMod 2023599269167163)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (4457267112703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (4457267112703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2023599269167163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_227
      · exact prime_fiftyNineBE_4457267112703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2023599269167163) ^ 1011799634583581 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2023599269167163) ^ 8914534225406 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2023599269167163) ^ 454 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_2287613501470169 : Nat.Prime 2287613501470169 := by
  apply lucas_primality 2287613501470169 (3 : ZMod 2287613501470169)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73, 1), (3917146406627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73, 1), (3917146406627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2287613501470169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_73
      · exact prime_fiftyNineBE_3917146406627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2287613501470169) ^ 1143806750735084 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2287613501470169) ^ 31337171253016 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2287613501470169) ^ 584 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3209084583180551 : Nat.Prime 3209084583180551 := by
  apply lucas_primality 3209084583180551 (11 : ZMod 3209084583180551)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (3377983771769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (3377983771769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3209084583180551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_3377983771769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3209084583180551) ^ 1604542291590275 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3209084583180551) ^ 641816916636110 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3209084583180551) ^ 168899188588450 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3209084583180551) ^ 950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4873632061734929 : Nat.Prime 4873632061734929 := by
  apply lucas_primality 4873632061734929 (3 : ZMod 4873632061734929)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (2664379, 1), (6724931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (2664379, 1), (6724931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4873632061734929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_2664379
      · exact prime_fiftyNineBE_6724931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4873632061734929) ^ 2436816030867464 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4873632061734929) ^ 286684238925584 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4873632061734929) ^ 1829181232 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4873632061734929) ^ 724711088 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_5240452641504559 : Nat.Prime 5240452641504559 := by
  apply lucas_primality 5240452641504559 (3 : ZMod 5240452641504559)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2879, 1), (303372272867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2879, 1), (303372272867, 1)] : List FactorBlock).map factorBlockValue).prod) = 5240452641504559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_2879
      · exact prime_fiftyNineBE_303372272867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5240452641504559) ^ 2620226320752279 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5240452641504559) ^ 1746817547168186 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5240452641504559) ^ 1820233637202 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5240452641504559) ^ 17274 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_6546192415931789 : Nat.Prime 6546192415931789 := by
  apply lucas_primality 6546192415931789 (2 : ZMod 6546192415931789)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4373, 1), (571069, 1), (655331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4373, 1), (571069, 1), (655331, 1)] : List FactorBlock).map factorBlockValue).prod) = 6546192415931789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_4373
      · exact prime_fiftyNineBE_571069
      · exact prime_fiftyNineBE_655331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6546192415931789) ^ 3273096207965894 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6546192415931789) ^ 1496956875356 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6546192415931789) ^ 11463049852 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6546192415931789) ^ 9989138948 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_7667532952123081 : Nat.Prime 7667532952123081 := by
  apply lucas_primality 7667532952123081 (13 : ZMod 7667532952123081)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (107, 1), (597159887237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (107, 1), (597159887237, 1)] : List FactorBlock).map factorBlockValue).prod) = 7667532952123081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_107
      · exact prime_fiftyNineBE_597159887237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7667532952123081) ^ 3833766476061540 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7667532952123081) ^ 2555844317374360 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7667532952123081) ^ 1533506590424616 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7667532952123081) ^ 71659186468440 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7667532952123081) ^ 12840 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_9462992465539853 : Nat.Prime 9462992465539853 := by
  apply lucas_primality 9462992465539853 (2 : ZMod 9462992465539853)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293, 1), (8074225653191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293, 1), (8074225653191, 1)] : List FactorBlock).map factorBlockValue).prod) = 9462992465539853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_293
      · exact prime_fiftyNineBE_8074225653191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9462992465539853) ^ 4731496232769926 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9462992465539853) ^ 32296902612764 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9462992465539853) ^ 1172 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_12742386381155087 : Nat.Prime 12742386381155087 := by
  apply lucas_primality 12742386381155087 (5 : ZMod 12742386381155087)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1823, 1), (120513613229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1823, 1), (120513613229, 1)] : List FactorBlock).map factorBlockValue).prod) = 12742386381155087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_1823
      · exact prime_fiftyNineBE_120513613229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12742386381155087) ^ 6371193190577543 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12742386381155087) ^ 439392633832934 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12742386381155087) ^ 6989789567282 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 12742386381155087) ^ 105734 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_16859313606063211 : Nat.Prime 16859313606063211 := by
  apply lucas_primality 16859313606063211 (2 : ZMod 16859313606063211)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89917, 1), (6249954071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89917, 1), (6249954071, 1)] : List FactorBlock).map factorBlockValue).prod) = 16859313606063211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_89917
      · exact prime_fiftyNineBE_6249954071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16859313606063211) ^ 8429656803031605 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16859313606063211) ^ 5619771202021070 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16859313606063211) ^ 3371862721212642 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16859313606063211) ^ 187498622130 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16859313606063211) ^ 2697510 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_31999418934012521 : Nat.Prime 31999418934012521 := by
  apply lucas_primality 31999418934012521 (3 : ZMod 31999418934012521)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (71, 1), (239, 1), (347, 1), (4684879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (71, 1), (239, 1), (347, 1), (4684879, 1)] : List FactorBlock).map factorBlockValue).prod) = 31999418934012521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_71
      · exact prime_fiftyNineBE_239
      · exact prime_fiftyNineBE_347
      · exact prime_fiftyNineBE_4684879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31999418934012521) ^ 15999709467006260 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 6399883786802504 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 1103428239103880 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 450696041324120 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 133888782150680 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 92217345631160 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31999418934012521) ^ 6830361880 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_35942859843273659 : Nat.Prime 35942859843273659 := by
  apply lucas_primality 35942859843273659 (2 : ZMod 35942859843273659)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (22067, 1), (259733, 1), (285049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (22067, 1), (259733, 1), (285049, 1)] : List FactorBlock).map factorBlockValue).prod) = 35942859843273659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_22067
      · exact prime_fiftyNineBE_259733
      · exact prime_fiftyNineBE_285049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35942859843273659) ^ 17971429921636829 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35942859843273659) ^ 3267532713024878 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35942859843273659) ^ 1628805902174 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35942859843273659) ^ 138383878226 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35942859843273659) ^ 126093618442 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_42899996362495871 : Nat.Prime 42899996362495871 := by
  apply lucas_primality 42899996362495871 (7 : ZMod 42899996362495871)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (329999972019199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (329999972019199, 1)] : List FactorBlock).map factorBlockValue).prod) = 42899996362495871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_329999972019199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42899996362495871) ^ 21449998181247935 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42899996362495871) ^ 8579999272499174 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42899996362495871) ^ 3299999720191990 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 42899996362495871) ^ 130 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_44768978642135843 : Nat.Prime 44768978642135843 := by
  apply lucas_primality 44768978642135843 (2 : ZMod 44768978642135843)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1063, 1), (66463, 1), (316835609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1063, 1), (66463, 1), (316835609, 1)] : List FactorBlock).map factorBlockValue).prod) = 44768978642135843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_1063
      · exact prime_fiftyNineBE_66463
      · exact prime_fiftyNineBE_316835609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44768978642135843) ^ 22384489321067921 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44768978642135843) ^ 42115690161934 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44768978642135843) ^ 673592504734 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 44768978642135843) ^ 141300338 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_51131117654751377 : Nat.Prime 51131117654751377 := by
  apply lucas_primality 51131117654751377 (3 : ZMod 51131117654751377)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (23, 1), (2917, 1), (4330203961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (23, 1), (2917, 1), (4330203961, 1)] : List FactorBlock).map factorBlockValue).prod) = 51131117654751377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_2917
      · exact prime_fiftyNineBE_4330203961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51131117654751377) ^ 25565558827375688 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 51131117654751377) ^ 4648283423159216 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 51131117654751377) ^ 2223092071945712 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 51131117654751377) ^ 17528665634128 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 51131117654751377) ^ 11808016 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_58483584740819149 : Nat.Prime 58483584740819149 := by
  apply lucas_primality 58483584740819149 (13 : ZMod 58483584740819149)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4873632061734929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4873632061734929, 1)] : List FactorBlock).map factorBlockValue).prod) = 58483584740819149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_4873632061734929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 58483584740819149) ^ 29241792370409574 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 58483584740819149) ^ 19494528246939716 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (13 : ZMod 58483584740819149) ^ 12 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_93060723480310627 : Nat.Prime 93060723480310627 := by
  apply lucas_primality 93060723480310627 (2 : ZMod 93060723480310627)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1723, 1), (32909, 1), (273536453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1723, 1), (32909, 1), (273536453, 1)] : List FactorBlock).map factorBlockValue).prod) = 93060723480310627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1723
      · exact prime_fiftyNineBE_32909
      · exact prime_fiftyNineBE_273536453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93060723480310627) ^ 46530361740155313 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93060723480310627) ^ 31020241160103542 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93060723480310627) ^ 54010866790662 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93060723480310627) ^ 2827819851114 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 93060723480310627) ^ 340213242 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_152219995188155803 : Nat.Prime 152219995188155803 := by
  apply lucas_primality 152219995188155803 (2 : ZMod 152219995188155803)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (46211291799683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (46211291799683, 1)] : List FactorBlock).map factorBlockValue).prod) = 152219995188155803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_61
      · exact prime_fiftyNineBE_46211291799683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152219995188155803) ^ 76109997594077901 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 152219995188155803) ^ 50739998396051934 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 152219995188155803) ^ 2495409757182882 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 152219995188155803) ^ 3294 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_180471368485863979 : Nat.Prime 180471368485863979 := by
  apply lucas_primality 180471368485863979 (10 : ZMod 180471368485863979)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (122393, 1), (547336159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (122393, 1), (547336159, 1)] : List FactorBlock).map factorBlockValue).prod) = 180471368485863979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_449
      · exact prime_fiftyNineBE_122393
      · exact prime_fiftyNineBE_547336159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 180471368485863979) ^ 90235684242931989 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 180471368485863979) ^ 60157122828621326 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 180471368485863979) ^ 401940687050922 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 180471368485863979) ^ 1474523612346 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 180471368485863979) ^ 329726742 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_181890516079204967 : Nat.Prime 181890516079204967 := by
  apply lucas_primality 181890516079204967 (5 : ZMod 181890516079204967)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (769, 1), (10751301340537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (769, 1), (10751301340537, 1)] : List FactorBlock).map factorBlockValue).prod) = 181890516079204967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_769
      · exact prime_fiftyNineBE_10751301340537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 181890516079204967) ^ 90945258039602483 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 181890516079204967) ^ 16535501461745906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 181890516079204967) ^ 236528629491814 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 181890516079204967) ^ 16918 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_247002708146486689 : Nat.Prime 247002708146486689 := by
  apply lucas_primality 247002708146486689 (7 : ZMod 247002708146486689)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (1777, 1), (43876210783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (1777, 1), (43876210783, 1)] : List FactorBlock).map factorBlockValue).prod) = 247002708146486689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_1777
      · exact prime_fiftyNineBE_43876210783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 247002708146486689) ^ 123501354073243344 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 247002708146486689) ^ 82334236048828896 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 247002708146486689) ^ 22454791649680608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 247002708146486689) ^ 138999835760544 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 247002708146486689) ^ 5629536 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_252229592723277931 : Nat.Prime 252229592723277931 := by
  apply lucas_primality 252229592723277931 (2 : ZMod 252229592723277931)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (383, 1), (9007, 1), (2437226251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (383, 1), (9007, 1), (2437226251, 1)] : List FactorBlock).map factorBlockValue).prod) = 252229592723277931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_383
      · exact prime_fiftyNineBE_9007
      · exact prime_fiftyNineBE_2437226251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252229592723277931) ^ 126114796361638965 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252229592723277931) ^ 84076530907759310 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252229592723277931) ^ 50445918544655586 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252229592723277931) ^ 658562905282710 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252229592723277931) ^ 28003729623990 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 252229592723277931) ^ 103490430 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_254806886598915293 : Nat.Prime 254806886598915293 := by
  apply lucas_primality 254806886598915293 (2 : ZMod 254806886598915293)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (111791, 1), (422309, 1), (1349317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (111791, 1), (422309, 1), (1349317, 1)] : List FactorBlock).map factorBlockValue).prod) = 254806886598915293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_111791
      · exact prime_fiftyNineBE_422309
      · exact prime_fiftyNineBE_1349317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 254806886598915293) ^ 127403443299457646 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254806886598915293) ^ 2279314851812 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254806886598915293) ^ 603365986988 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254806886598915293) ^ 188841381676 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_292932118566493121 : Nat.Prime 292932118566493121 := by
  apply lucas_primality 292932118566493121 (6 : ZMod 292932118566493121)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 1), (13, 1), (700027, 1), (9144631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 1), (13, 1), (700027, 1), (9144631, 1)] : List FactorBlock).map factorBlockValue).prod) = 292932118566493121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_700027
      · exact prime_fiftyNineBE_9144631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 292932118566493121) ^ 146466059283246560 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 292932118566493121) ^ 58586423713298624 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 292932118566493121) ^ 26630192596953920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 292932118566493121) ^ 22533239889730240 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 292932118566493121) ^ 418458314560 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 292932118566493121) ^ 32033235520 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_756578720023024957 : Nat.Prime 756578720023024957 := by
  apply lucas_primality 756578720023024957 (2 : ZMod 756578720023024957)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (883, 1), (1171, 1), (4507, 1), (13529063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (883, 1), (1171, 1), (4507, 1), (13529063, 1)] : List FactorBlock).map factorBlockValue).prod) = 756578720023024957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_883
      · exact prime_fiftyNineBE_1171
      · exact prime_fiftyNineBE_4507
      · exact prime_fiftyNineBE_13529063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 756578720023024957) ^ 378289360011512478 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 756578720023024957) ^ 252192906674341652 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 756578720023024957) ^ 856827542494932 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 756578720023024957) ^ 646096259626836 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 756578720023024957) ^ 167867477262708 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 756578720023024957) ^ 55922477412 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_966876197719064057 : Nat.Prime 966876197719064057 := by
  apply lucas_primality 966876197719064057 (3 : ZMod 966876197719064057)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (223, 1), (72109, 1), (174790607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (223, 1), (72109, 1), (174790607, 1)] : List FactorBlock).map factorBlockValue).prod) = 966876197719064057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_223
      · exact prime_fiftyNineBE_72109
      · exact prime_fiftyNineBE_174790607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 966876197719064057) ^ 483438098859532028 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 966876197719064057) ^ 22485492970210792 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 966876197719064057) ^ 4335767702776072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 966876197719064057) ^ 13408537044184 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 966876197719064057) ^ 5531625608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_989663192306689309 : Nat.Prime 989663192306689309 := by
  apply lucas_primality 989663192306689309 (2 : ZMod 989663192306689309)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (1559, 1), (10177, 1), (26932891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (1559, 1), (10177, 1), (26932891, 1)] : List FactorBlock).map factorBlockValue).prod) = 989663192306689309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_193
      · exact prime_fiftyNineBE_1559
      · exact prime_fiftyNineBE_10177
      · exact prime_fiftyNineBE_26932891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 989663192306689309) ^ 494831596153344654 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 989663192306689309) ^ 329887730768896436 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 989663192306689309) ^ 5127788561174556 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 989663192306689309) ^ 634806409433412 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 989663192306689309) ^ 97245081291804 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 989663192306689309) ^ 36745523988 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1003262195287592263 : Nat.Prime 1003262195287592263 := by
  apply lucas_primality 1003262195287592263 (3 : ZMod 1003262195287592263)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (599, 1), (8459066417831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (599, 1), (8459066417831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1003262195287592263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_599
      · exact prime_fiftyNineBE_8459066417831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1003262195287592263) ^ 501631097643796131 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003262195287592263) ^ 334420731762530754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003262195287592263) ^ 91205654117053842 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003262195287592263) ^ 1674895150730538 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003262195287592263) ^ 118602 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1296050990954783149 : Nat.Prime 1296050990954783149 := by
  apply lucas_primality 1296050990954783149 (2 : ZMod 1296050990954783149)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (153530929, 1), (234489667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (153530929, 1), (234489667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296050990954783149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_153530929
      · exact prime_fiftyNineBE_234489667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1296050990954783149) ^ 648025495477391574 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296050990954783149) ^ 432016996984927716 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296050990954783149) ^ 8441628012 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296050990954783149) ^ 5527113444 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1508191398886036663 : Nat.Prime 1508191398886036663 := by
  apply lucas_primality 1508191398886036663 (5 : ZMod 1508191398886036663)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (2731, 1), (190562033449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (2731, 1), (190562033449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508191398886036663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_2731
      · exact prime_fiftyNineBE_190562033449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1508191398886036663) ^ 754095699443018331 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508191398886036663) ^ 502730466295345554 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508191398886036663) ^ 215455914126576666 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508191398886036663) ^ 65573539082001594 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508191398886036663) ^ 552248772935202 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1508191398886036663) ^ 7914438 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_6716758866059818957 : Nat.Prime 6716758866059818957 := by
  apply lucas_primality 6716758866059818957 (11 : ZMod 6716758866059818957)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (7667532952123081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (7667532952123081, 1)] : List FactorBlock).map factorBlockValue).prod) = 6716758866059818957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_73
      · exact prime_fiftyNineBE_7667532952123081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6716758866059818957) ^ 3358379433029909478 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6716758866059818957) ^ 2238919622019939652 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6716758866059818957) ^ 92010395425476972 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 6716758866059818957) ^ 876 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_10532944287843957677 : Nat.Prime 10532944287843957677 := by
  apply lucas_primality 10532944287843957677 (2 : ZMod 10532944287843957677)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6823, 1), (15091, 1), (25573867183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6823, 1), (15091, 1), (25573867183, 1)] : List FactorBlock).map factorBlockValue).prod) = 10532944287843957677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_6823
      · exact prime_fiftyNineBE_15091
      · exact prime_fiftyNineBE_25573867183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10532944287843957677) ^ 5266472143921978838 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10532944287843957677) ^ 1543740918634612 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10532944287843957677) ^ 697961983158436 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10532944287843957677) ^ 411863572 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_15552611891457397789 : Nat.Prime 15552611891457397789 := by
  apply lucas_primality 15552611891457397789 (6 : ZMod 15552611891457397789)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1296050990954783149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1296050990954783149, 1)] : List FactorBlock).map factorBlockValue).prod) = 15552611891457397789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1296050990954783149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 15552611891457397789) ^ 7776305945728698894 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 15552611891457397789) ^ 5184203963819132596 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 15552611891457397789) ^ 12 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_25192162196718408407 : Nat.Prime 25192162196718408407 := by
  apply lucas_primality 25192162196718408407 (5 : ZMod 25192162196718408407)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (292932118566493121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (292932118566493121, 1)] : List FactorBlock).map factorBlockValue).prod) = 25192162196718408407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_292932118566493121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25192162196718408407) ^ 12596081098359204203 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 25192162196718408407) ^ 585864237132986242 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 25192162196718408407) ^ 86 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_25664393549388243841 : Nat.Prime 25664393549388243841 := by
  apply lucas_primality 25664393549388243841 (17 : ZMod 25664393549388243841)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (10505477, 1), (1272371701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (10505477, 1), (1272371701, 1)] : List FactorBlock).map factorBlockValue).prod) = 25664393549388243841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_10505477
      · exact prime_fiftyNineBE_1272371701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 25664393549388243841) ^ 12832196774694121920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 25664393549388243841) ^ 8554797849796081280 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 25664393549388243841) ^ 5132878709877648768 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 25664393549388243841) ^ 2442953665920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (17 : ZMod 25664393549388243841) ^ 20170515840 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_32527859129022172009 : Nat.Prime 32527859129022172009 := by
  apply lucas_primality 32527859129022172009 (7 : ZMod 32527859129022172009)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (349, 1), (367, 1), (739, 1), (842285623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (349, 1), (367, 1), (739, 1), (842285623, 1)] : List FactorBlock).map factorBlockValue).prod) = 32527859129022172009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_349
      · exact prime_fiftyNineBE_367
      · exact prime_fiftyNineBE_739
      · exact prime_fiftyNineBE_842285623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32527859129022172009) ^ 16263929564511086004 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 10842619709674057336 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 1913403478177774824 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 93203034753645192 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 88631768743929624 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 44016047535889272 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 32527859129022172009) ^ 38618561496 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_47784599467265551291 : Nat.Prime 47784599467265551291 := by
  apply lucas_primality 47784599467265551291 (2 : ZMod 47784599467265551291)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (201151, 1), (7918528778093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (201151, 1), (7918528778093, 1)] : List FactorBlock).map factorBlockValue).prod) = 47784599467265551291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_201151
      · exact prime_fiftyNineBE_7918528778093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47784599467265551291) ^ 23892299733632775645 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47784599467265551291) ^ 15928199822421850430 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47784599467265551291) ^ 9556919893453110258 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47784599467265551291) ^ 237555863342790 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 47784599467265551291) ^ 6034530 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_55973928455542464641 : Nat.Prime 55973928455542464641 := by
  apply lucas_primality 55973928455542464641 (3 : ZMod 55973928455542464641)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (13, 2), (57809, 1), (1278867683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (13, 2), (57809, 1), (1278867683, 1)] : List FactorBlock).map factorBlockValue).prod) = 55973928455542464641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_57809
      · exact prime_fiftyNineBE_1278867683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55973928455542464641) ^ 27986964227771232320 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55973928455542464641) ^ 11194785691108492928 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55973928455542464641) ^ 7996275493648923520 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55973928455542464641) ^ 4305686804272497280 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55973928455542464641) ^ 968256300152960 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 55973928455542464641) ^ 43768350080 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_61233083858625954307 : Nat.Prime 61233083858625954307 := by
  apply lucas_primality 61233083858625954307 (2 : ZMod 61233083858625954307)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1559, 1), (6546192415931789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1559, 1), (6546192415931789, 1)] : List FactorBlock).map factorBlockValue).prod) = 61233083858625954307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1559
      · exact prime_fiftyNineBE_6546192415931789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61233083858625954307) ^ 30616541929312977153 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61233083858625954307) ^ 20411027952875318102 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61233083858625954307) ^ 39277154495590734 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61233083858625954307) ^ 9354 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_97116087187973391737 : Nat.Prime 97116087187973391737 := by
  apply lucas_primality 97116087187973391737 (3 : ZMod 97116087187973391737)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1163, 1), (30853, 1), (30756108923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1163, 1), (30853, 1), (30756108923, 1)] : List FactorBlock).map factorBlockValue).prod) = 97116087187973391737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_1163
      · exact prime_fiftyNineBE_30853
      · exact prime_fiftyNineBE_30756108923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97116087187973391737) ^ 48558043593986695868 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 97116087187973391737) ^ 8828735198906671976 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 97116087187973391737) ^ 83504804116916072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 97116087187973391737) ^ 3147703211615512 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 97116087187973391737) ^ 3157619432 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_104600021174205797311 : Nat.Prime 104600021174205797311 := by
  apply lucas_primality 104600021174205797311 (6 : ZMod 104600021174205797311)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (397, 1), (1063, 1), (14940379019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 1), (397, 1), (1063, 1), (14940379019, 1)] : List FactorBlock).map factorBlockValue).prod) = 104600021174205797311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_79
      · exact prime_fiftyNineBE_397
      · exact prime_fiftyNineBE_1063
      · exact prime_fiftyNineBE_14940379019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 104600021174205797311) ^ 52300010587102898655 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 34866673724735265770 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 20920004234841159462 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 14942860167743685330 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 1324050900939313890 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 263476123864498230 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 98400772506308370 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 104600021174205797311) ^ 7001162490 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_216469144278837435569 : Nat.Prime 216469144278837435569 := by
  apply lucas_primality 216469144278837435569 (3 : ZMod 216469144278837435569)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (1553, 1), (21991, 1), (38273, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (1553, 1), (21991, 1), (38273, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 216469144278837435569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_1553
      · exact prime_fiftyNineBE_21991
      · exact prime_fiftyNineBE_38273
      · exact prime_fiftyNineBE_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 216469144278837435569) ^ 108234572139418717784 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 19679013116257948688 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 12733479075225731504 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 139387729735246256 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 9843533458180048 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 5655923086218416 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 216469144278837435569) ^ 3910844325826768 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_290110437020130138271 : Nat.Prime 290110437020130138271 := by
  apply lucas_primality 290110437020130138271 (6 : ZMod 290110437020130138271)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (109, 1), (112459, 1), (262966319813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (109, 1), (112459, 1), (262966319813, 1)] : List FactorBlock).map factorBlockValue).prod) = 290110437020130138271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_109
      · exact prime_fiftyNineBE_112459
      · exact prime_fiftyNineBE_262966319813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 290110437020130138271) ^ 145055218510065069135 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 290110437020130138271) ^ 96703479006710046090 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 290110437020130138271) ^ 58022087404026027654 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 290110437020130138271) ^ 2661563642386515030 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 290110437020130138271) ^ 2579699597365530 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 290110437020130138271) ^ 1103222790 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_3330915123102412197169 : Nat.Prime 3330915123102412197169 := by
  apply lucas_primality 3330915123102412197169 (14 : ZMod 3330915123102412197169)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (1009, 1), (1434229, 1), (15984218527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (1009, 1), (1434229, 1), (15984218527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330915123102412197169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_1009
      · exact prime_fiftyNineBE_1434229
      · exact prime_fiftyNineBE_15984218527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 3330915123102412197169) ^ 1665457561551206098584 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 3330915123102412197169) ^ 1110305041034137399056 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 3330915123102412197169) ^ 3301204284541538352 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 3330915123102412197169) ^ 2322443015098992 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (14 : ZMod 3330915123102412197169) ^ 208387736784 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_9758072417945175613931 : Nat.Prime 9758072417945175613931 := by
  apply lucas_primality 9758072417945175613931 (6 : ZMod 9758072417945175613931)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (230563, 1), (248957664447083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (230563, 1), (248957664447083, 1)] : List FactorBlock).map factorBlockValue).prod) = 9758072417945175613931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_230563
      · exact prime_fiftyNineBE_248957664447083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9758072417945175613931) ^ 4879036208972587806965 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9758072417945175613931) ^ 1951614483589035122786 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9758072417945175613931) ^ 574004259879127977290 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9758072417945175613931) ^ 42322802956004110 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 9758072417945175613931) ^ 39195710 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_13345080102925986360467 : Nat.Prime 13345080102925986360467 := by
  apply lucas_primality 13345080102925986360467 (2 : ZMod 13345080102925986360467)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (290110437020130138271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (290110437020130138271, 1)] : List FactorBlock).map factorBlockValue).prod) = 13345080102925986360467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_23
      · exact prime_fiftyNineBE_290110437020130138271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13345080102925986360467) ^ 6672540051462993180233 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13345080102925986360467) ^ 580220874040260276542 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13345080102925986360467) ^ 46 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_14916244952446253440051 : Nat.Prime 14916244952446253440051 := by
  apply lucas_primality 14916244952446253440051 (10 : ZMod 14916244952446253440051)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (67, 1), (1459, 1), (13397, 1), (5841000499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (67, 1), (1459, 1), (13397, 1), (5841000499, 1)] : List FactorBlock).map factorBlockValue).prod) = 14916244952446253440051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_67
      · exact prime_fiftyNineBE_1459
      · exact prime_fiftyNineBE_13397
      · exact prime_fiftyNineBE_5841000499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 14916244952446253440051) ^ 7458122476223126720025 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 4972081650815417813350 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 2983248990489250688010 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 1147403457880481033850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 222630521678302290150 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 10223608603458706950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 1113401877468556650 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 14916244952446253440051) ^ 2553714034950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_21614960208008885419957 : Nat.Prime 21614960208008885419957 := by
  apply lucas_primality 21614960208008885419957 (2 : ZMod 21614960208008885419957)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (9267619147, 1), (11432891837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (9267619147, 1), (11432891837, 1)] : List FactorBlock).map factorBlockValue).prod) = 21614960208008885419957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_17
      · exact prime_fiftyNineBE_9267619147
      · exact prime_fiftyNineBE_11432891837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21614960208008885419957) ^ 10807480104004442709978 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21614960208008885419957) ^ 7204986736002961806652 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21614960208008885419957) ^ 1271468247529934436468 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21614960208008885419957) ^ 2332309934748 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 21614960208008885419957) ^ 1890594305988 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34226014084201047864863 : Nat.Prime 34226014084201047864863 := by
  apply lucas_primality 34226014084201047864863 (5 : ZMod 34226014084201047864863)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (454457779, 1), (372830483089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (454457779, 1), (372830483089, 1)] : List FactorBlock).map factorBlockValue).prod) = 34226014084201047864863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_101
      · exact prime_fiftyNineBE_454457779
      · exact prime_fiftyNineBE_372830483089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34226014084201047864863) ^ 17113007042100523932431 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34226014084201047864863) ^ 338871426576247998662 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34226014084201047864863) ^ 75311757583978 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34226014084201047864863) ^ 91800471358 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34911784865899156247833 : Nat.Prime 34911784865899156247833 := by
  apply lucas_primality 34911784865899156247833 (5 : ZMod 34911784865899156247833)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (263, 1), (557, 1), (331711, 1), (1575565247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (263, 1), (557, 1), (331711, 1), (1575565247, 1)] : List FactorBlock).map factorBlockValue).prod) = 34911784865899156247833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_19
      · exact prime_fiftyNineBE_263
      · exact prime_fiftyNineBE_557
      · exact prime_fiftyNineBE_331711
      · exact prime_fiftyNineBE_1575565247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34911784865899156247833) ^ 17455892432949578123916 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 11637261621966385415944 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 1837462361363113486728 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 132744429147905537064 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 62678249310411411576 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 105247594640814312 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34911784865899156247833) ^ 22158260302056 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_38296838175349204035787 : Nat.Prime 38296838175349204035787 := by
  apply lucas_primality 38296838175349204035787 (2 : ZMod 38296838175349204035787)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (137, 1), (367, 2), (4738447939879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (137, 1), (367, 2), (4738447939879, 1)] : List FactorBlock).map factorBlockValue).prod) = 38296838175349204035787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_73
      · exact prime_fiftyNineBE_137
      · exact prime_fiftyNineBE_367
      · exact prime_fiftyNineBE_4738447939879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38296838175349204035787) ^ 19148419087674602017893 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38296838175349204035787) ^ 12765612725116401345262 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38296838175349204035787) ^ 524614221580126082682 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38296838175349204035787) ^ 279538964783570832378 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38296838175349204035787) ^ 104351057698499193558 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 38296838175349204035787) ^ 8082148134 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_57829432781406132478391 : Nat.Prime 57829432781406132478391 := by
  apply lucas_primality 57829432781406132478391 (7 : ZMod 57829432781406132478391)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (11743, 1), (44768978642135843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (11743, 1), (44768978642135843, 1)] : List FactorBlock).map factorBlockValue).prod) = 57829432781406132478391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_11743
      · exact prime_fiftyNineBE_44768978642135843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 57829432781406132478391) ^ 28914716390703066239195 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 57829432781406132478391) ^ 11565886556281226495678 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 57829432781406132478391) ^ 5257221161946012043490 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 57829432781406132478391) ^ 4924587650634942730 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (7 : ZMod 57829432781406132478391) ^ 1291730 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_88011348327137979472907 : Nat.Prime 88011348327137979472907 := by
  apply lucas_primality 88011348327137979472907 (2 : ZMod 88011348327137979472907)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2447, 1), (760657, 1), (23642088741307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2447, 1), (760657, 1), (23642088741307, 1)] : List FactorBlock).map factorBlockValue).prod) = 88011348327137979472907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_2447
      · exact prime_fiftyNineBE_760657
      · exact prime_fiftyNineBE_23642088741307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88011348327137979472907) ^ 44005674163568989736453 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 88011348327137979472907) ^ 35967040591392717398 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 88011348327137979472907) ^ 115704382299956458 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 88011348327137979472907) ^ 3722655358 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_98809317695715538199501 : Nat.Prime 98809317695715538199501 := by
  apply lucas_primality 98809317695715538199501 (2 : ZMod 98809317695715538199501)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (5643041, 1), (35019882965839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (5643041, 1), (35019882965839, 1)] : List FactorBlock).map factorBlockValue).prod) = 98809317695715538199501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_5643041
      · exact prime_fiftyNineBE_35019882965839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 98809317695715538199501) ^ 49404658847857769099750 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 98809317695715538199501) ^ 19761863539143107639900 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 98809317695715538199501) ^ 17509941482919500 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 98809317695715538199501) ^ 2821520500 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_159086235302855448401059 : Nat.Prime 159086235302855448401059 := by
  apply lucas_primality 159086235302855448401059 (10 : ZMod 159086235302855448401059)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (2867092663, 1), (45555790487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (2867092663, 1), (45555790487, 1)] : List FactorBlock).map factorBlockValue).prod) = 159086235302855448401059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_2867092663
      · exact prime_fiftyNineBE_45555790487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 159086235302855448401059) ^ 79543117651427724200529 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 159086235302855448401059) ^ 53028745100951816133686 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 159086235302855448401059) ^ 22726605043265064057294 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 159086235302855448401059) ^ 5485732251822601669002 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 159086235302855448401059) ^ 55486952813166 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 159086235302855448401059) ^ 3492118863534 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_374376052823457031897651 : Nat.Prime 374376052823457031897651 := by
  apply lucas_primality 374376052823457031897651 (2 : ZMod 374376052823457031897651)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (486591359, 1), (5129232786389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (486591359, 1), (5129232786389, 1)] : List FactorBlock).map factorBlockValue).prod) = 374376052823457031897651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_486591359
      · exact prime_fiftyNineBE_5129232786389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 374376052823457031897651) ^ 187188026411728515948825 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374376052823457031897651) ^ 124792017607819010632550 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374376052823457031897651) ^ 74875210564691406379530 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374376052823457031897651) ^ 769384917958350 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374376052823457031897651) ^ 72988703850 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1040929790065310384611039 : Nat.Prime 1040929790065310384611039 := by
  apply lucas_primality 1040929790065310384611039 (6 : ZMod 1040929790065310384611039)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (57829432781406132478391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (57829432781406132478391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040929790065310384611039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_57829432781406132478391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1040929790065310384611039) ^ 520464895032655192305519 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1040929790065310384611039) ^ 346976596688436794870346 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1040929790065310384611039) ^ 18 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_1141782003569477414115929 : Nat.Prime 1141782003569477414115929 := by
  apply lucas_primality 1141782003569477414115929 (3 : ZMod 1141782003569477414115929)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (29, 1), (13417, 1), (87407, 1), (381505575331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (29, 1), (13417, 1), (87407, 1), (381505575331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141782003569477414115929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_29
      · exact prime_fiftyNineBE_13417
      · exact prime_fiftyNineBE_87407
      · exact prime_fiftyNineBE_381505575331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1141782003569477414115929) ^ 570891001784738707057964 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141782003569477414115929) ^ 103798363960861583101448 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141782003569477414115929) ^ 39371793226533703935032 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141782003569477414115929) ^ 85099649964185541784 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141782003569477414115929) ^ 13062821096359300904 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141782003569477414115929) ^ 2992831762888 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4988111138591712970764469 : Nat.Prime 4988111138591712970764469 := by
  apply lucas_primality 4988111138591712970764469 (6 : ZMod 4988111138591712970764469)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (293, 1), (8689, 1), (31672337, 1), (5155103011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (293, 1), (8689, 1), (31672337, 1), (5155103011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4988111138591712970764469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_293
      · exact prime_fiftyNineBE_8689
      · exact prime_fiftyNineBE_31672337
      · exact prime_fiftyNineBE_5155103011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4988111138591712970764469) ^ 2494055569295856485382234 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4988111138591712970764469) ^ 1662703712863904323588156 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4988111138591712970764469) ^ 17024270097582638125476 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4988111138591712970764469) ^ 574071945976719181812 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4988111138591712970764469) ^ 157491098260027764 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 4988111138591712970764469) ^ 967606491654588 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_36596928731409503768714761 : Nat.Prime 36596928731409503768714761 := by
  apply lucas_primality 36596928731409503768714761 (11 : ZMod 36596928731409503768714761)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (4363, 1), (526041757, 1), (6327594893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (4363, 1), (526041757, 1), (6327594893, 1)] : List FactorBlock).map factorBlockValue).prod) = 36596928731409503768714761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_4363
      · exact prime_fiftyNineBE_526041757
      · exact prime_fiftyNineBE_6327594893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36596928731409503768714761) ^ 18298464365704751884357380 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 12198976243803167922904920 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 7319385746281900753742952 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 5228132675915643395530680 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 8388019420446826442520 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 69570387225760680 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (11 : ZMod 36596928731409503768714761) ^ 5783702868193320 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_63702051289558460441251447 : Nat.Prime 63702051289558460441251447 := by
  apply lucas_primality 63702051289558460441251447 (3 : ZMod 63702051289558460441251447)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (300583, 1), (247002708146486689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (300583, 1), (247002708146486689, 1)] : List FactorBlock).map factorBlockValue).prod) = 63702051289558460441251447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_13
      · exact prime_fiftyNineBE_300583
      · exact prime_fiftyNineBE_247002708146486689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63702051289558460441251447) ^ 31851025644779230220625723 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 63702051289558460441251447) ^ 21234017096519486813750482 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 63702051289558460441251447) ^ 5791095571778041858295586 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 63702051289558460441251447) ^ 4900157791504496957019342 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 63702051289558460441251447) ^ 211928323589685579162 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 63702051289558460441251447) ^ 257900214 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_157103031896546203115248501 : Nat.Prime 157103031896546203115248501 := by
  apply lucas_primality 157103031896546203115248501 (6 : ZMod 157103031896546203115248501)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 3), (34911784865899156247833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 3), (34911784865899156247833, 1)] : List FactorBlock).map factorBlockValue).prod) = 157103031896546203115248501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_34911784865899156247833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 157103031896546203115248501) ^ 78551515948273101557624250 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 157103031896546203115248501) ^ 52367677298848734371749500 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 157103031896546203115248501) ^ 31420606379309240623049700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (6 : ZMod 157103031896546203115248501) ^ 4500 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_178398327780221263895576303 : Nat.Prime 178398327780221263895576303 := by
  apply lucas_primality 178398327780221263895576303 (5 : ZMod 178398327780221263895576303)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (63773, 1), (32527859129022172009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (63773, 1), (32527859129022172009, 1)] : List FactorBlock).map factorBlockValue).prod) = 178398327780221263895576303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_43
      · exact prime_fiftyNineBE_63773
      · exact prime_fiftyNineBE_32527859129022172009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 178398327780221263895576303) ^ 89199163890110631947788151 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 178398327780221263895576303) ^ 4148798320470261951059914 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 178398327780221263895576303) ^ 2797395885095906792774 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 178398327780221263895576303) ^ 5484478 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_410316153894508906959825497 : Nat.Prime 410316153894508906959825497 := by
  apply lucas_primality 410316153894508906959825497 (3 : ZMod 410316153894508906959825497)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (374376052823457031897651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (374376052823457031897651, 1)] : List FactorBlock).map factorBlockValue).prod) = 410316153894508906959825497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_137
      · exact prime_fiftyNineBE_374376052823457031897651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 410316153894508906959825497) ^ 205158076947254453479912748 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 410316153894508906959825497) ^ 2995008422587656255181208 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 410316153894508906959825497) ^ 1096 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_634124965109695583483366677 : Nat.Prime 634124965109695583483366677 := by
  apply lucas_primality 634124965109695583483366677 (2 : ZMod 634124965109695583483366677)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (428227, 1), (1003262195287592263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (428227, 1), (1003262195287592263, 1)] : List FactorBlock).map factorBlockValue).prod) = 634124965109695583483366677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_41
      · exact prime_fiftyNineBE_428227
      · exact prime_fiftyNineBE_1003262195287592263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 634124965109695583483366677) ^ 317062482554847791741683338 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 634124965109695583483366677) ^ 211374988369898527827788892 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 634124965109695583483366677) ^ 15466462563651111792277236 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 634124965109695583483366677) ^ 1480815000244486180188 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 634124965109695583483366677) ^ 632063052 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_4359609135129157136448145901 : Nat.Prime 4359609135129157136448145901 := by
  apply lucas_primality 4359609135129157136448145901 (2 : ZMod 4359609135129157136448145901)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (448907, 1), (97116087187973391737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (448907, 1), (97116087187973391737, 1)] : List FactorBlock).map factorBlockValue).prod) = 4359609135129157136448145901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_448907
      · exact prime_fiftyNineBE_97116087187973391737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4359609135129157136448145901) ^ 2179804567564578568224072950 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4359609135129157136448145901) ^ 871921827025831427289629180 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4359609135129157136448145901) ^ 9711608718797339173700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4359609135129157136448145901) ^ 44890700 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_11625624360344419030528389083 : Nat.Prime 11625624360344419030528389083 := by
  apply lucas_primality 11625624360344419030528389083 (2 : ZMod 11625624360344419030528389083)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (97, 1), (6653, 1), (283553, 1), (58935099508003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (97, 1), (6653, 1), (283553, 1), (58935099508003, 1)] : List FactorBlock).map factorBlockValue).prod) = 11625624360344419030528389083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_7
      · exact prime_fiftyNineBE_11
      · exact prime_fiftyNineBE_97
      · exact prime_fiftyNineBE_6653
      · exact prime_fiftyNineBE_283553
      · exact prime_fiftyNineBE_58935099508003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11625624360344419030528389083) ^ 5812812180172209515264194541 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 1660803480049202718646912726 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 1056874941849492639138944462 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 119851797529323907531220506 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 1747425877099717274992994 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 40999828463618508816794 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344419030528389083) ^ 197261469945694 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_34876873081033257091585167217 : Nat.Prime 34876873081033257091585167217 := by
  apply lucas_primality 34876873081033257091585167217 (5 : ZMod 34876873081033257091585167217)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (106693141, 1), (252229592723277931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (106693141, 1), (252229592723277931, 1)] : List FactorBlock).map factorBlockValue).prod) = 34876873081033257091585167217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_106693141
      · exact prime_fiftyNineBE_252229592723277931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34876873081033257091585167217) ^ 17438436540516628545792583608 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34876873081033257091585167217) ^ 11625624360344419030528389072 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34876873081033257091585167217) ^ 326889552169368198576 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (5 : ZMod 34876873081033257091585167217) ^ 138274310736 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_69753746162066514183170334433 : Nat.Prime 69753746162066514183170334433 := by
  apply lucas_primality 69753746162066514183170334433 (10 : ZMod 69753746162066514183170334433)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (106693141, 1), (252229592723277931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (106693141, 1), (252229592723277931, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_106693141
      · exact prime_fiftyNineBE_252229592723277931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 69753746162066514183170334433) ^ 34876873081033257091585167216 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 69753746162066514183170334433) ^ 23251248720688838061056778144 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 69753746162066514183170334433) ^ 653779104338736397152 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (10 : ZMod 69753746162066514183170334433) ^ 276548621472 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_69753746162066514183170334461 : Nat.Prime 69753746162066514183170334461 := by
  apply lucas_primality 69753746162066514183170334461 (2 : ZMod 69753746162066514183170334461)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (709, 1), (32316149, 1), (152219995188155803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (709, 1), (32316149, 1), (152219995188155803, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_5
      · exact prime_fiftyNineBE_709
      · exact prime_fiftyNineBE_32316149
      · exact prime_fiftyNineBE_152219995188155803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69753746162066514183170334461) ^ 34876873081033257091585167230 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 69753746162066514183170334461) ^ 13950749232413302836634066892 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 69753746162066514183170334461) ^ 98383280905594519299252940 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 69753746162066514183170334461) ^ 2158479531768049286540 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (2 : ZMod 69753746162066514183170334461) ^ 458242992820 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem prime_fiftyNineBE_69753746162066514183170334487 : Nat.Prime 69753746162066514183170334487 := by
  apply lucas_primality 69753746162066514183170334487 (3 : ZMod 69753746162066514183170334487)
  · rw [← fiftyNineBEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7559, 1), (14853086021, 1), (11505161919931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7559, 1), (14853086021, 1), (11505161919931, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyNineBE_2
      · exact prime_fiftyNineBE_3
      · exact prime_fiftyNineBE_7559
      · exact prime_fiftyNineBE_14853086021
      · exact prime_fiftyNineBE_11505161919931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69753746162066514183170334487) ^ 34876873081033257091585167243 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69753746162066514183170334487) ^ 23251248720688838061056778162 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69753746162066514183170334487) ^ 9227906622842507498765754 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69753746162066514183170334487) ^ 4696246023448955166 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69753746162066514183170334487) ^ 6062821770567906 ≠ 1
      rw [← fiftyNineBEFastPow_eq_pow]
      decide

private theorem phi_fiftyNineBE_69753746162066514183170334400 : Nat.totient 69753746162066514183170334400 = 27901436310530805370010122240 := by
  rw [← show ((([(2, 6), (5, 2), (448907, 1), (97116087187973391737, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_448907, prime_fiftyNineBE_97116087187973391737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334401 : Nat.totient 69753746162066514183170334401 = 55259688990492266727963985920 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (59093, 1), (216469144278837435569, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_7, prime_fiftyNineBE_19, prime_fiftyNineBE_41, prime_fiftyNineBE_59093, prime_fiftyNineBE_216469144278837435569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334402 : Nat.totient 69753746162066514183170334402 = 23250798751571066093076630144 := by
  rw [← show ((([(2, 1), (3, 1), (51673, 1), (314158636567, 1), (716149357237, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_51673, prime_fiftyNineBE_314158636567, prime_fiftyNineBE_716149357237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334403 : Nat.totient 69753746162066514183170334403 = 67703485826571287955300997920 := by
  rw [← show ((([(59, 1), (79, 1), (1581466291, 1), (9462992465539853, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_59, prime_fiftyNineBE_79, prime_fiftyNineBE_1581466291, prime_fiftyNineBE_9462992465539853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334404 : Nat.totient 69753746162066514183170334404 = 30326250119983449800872112640 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (20693, 1), (3330915123102412197169, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_11, prime_fiftyNineBE_23, prime_fiftyNineBE_20693, prime_fiftyNineBE_3330915123102412197169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334405 : Nat.totient 69753746162066514183170334405 = 35013644838793893227875550208 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (119281663, 1), (254806886598915293, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_17, prime_fiftyNineBE_119281663, prime_fiftyNineBE_254806886598915293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334406 : Nat.totient 69753746162066514183170334406 = 34114475758977259694689665024 := by
  rw [← show ((([(2, 1), (47, 1), (3329, 1), (3467, 1), (142297, 1), (451831288860319, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_47, prime_fiftyNineBE_3329, prime_fiftyNineBE_3467, prime_fiftyNineBE_142297, prime_fiftyNineBE_451831288860319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334407 : Nat.totient 69753746162066514183170334407 = 67828792691880337898486880000 := by
  rw [← show ((([(37, 1), (1721, 1), (273719, 1), (2008339, 1), (1992704839751, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_37, prime_fiftyNineBE_1721, prime_fiftyNineBE_273719, prime_fiftyNineBE_2008339, prime_fiftyNineBE_1992704839751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334408 : Nat.totient 69753746162066514183170334408 = 19904733581833188847265587200 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (811, 1), (60497, 1), (3984521, 1), (2123867609783, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_7, prime_fiftyNineBE_811, prime_fiftyNineBE_60497, prime_fiftyNineBE_3984521, prime_fiftyNineBE_2123867609783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334409 : Nat.totient 69753746162066514183170334409 = 68771299032131351398831240320 := by
  rw [← show ((([(71, 1), (77100717217, 1), (12742386381155087, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_71, prime_fiftyNineBE_77100717217, prime_fiftyNineBE_12742386381155087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334410 : Nat.totient 69753746162066514183170334410 = 25754364120296857994563491072 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (30029, 1), (3409687, 1), (5240452641504559, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_13, prime_fiftyNineBE_30029, prime_fiftyNineBE_3409687, prime_fiftyNineBE_5240452641504559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334411 : Nat.totient 69753746162066514183170334411 = 46502467608887771229603558600 := by
  rw [← show ((([(3, 1), (1558787, 1), (14916244952446253440051, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_1558787, prime_fiftyNineBE_14916244952446253440051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334412 : Nat.totient 69753746162066514183170334412 = 34836459550923656607272439936 := by
  rw [← show ((([(2, 2), (863, 1), (8833119349, 1), (2287613501470169, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_863, prime_fiftyNineBE_8833119349, prime_fiftyNineBE_2287613501470169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334413 : Nat.totient 69753746162066514183170334413 = 69753746057466493008297675420 := by
  rw [← show ((([(666861683, 1), (104600021174205797311, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_666861683, prime_fiftyNineBE_104600021174205797311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334414 : Nat.totient 69753746162066514183170334414 = 23248508855344711890730848000 := by
  rw [← show ((([(2, 1), (3, 2), (8501, 1), (4898449, 1), (93060723480310627, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_8501, prime_fiftyNineBE_4898449, prime_fiftyNineBE_93060723480310627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334415 : Nat.totient 69753746162066514183170334415 = 43477837623260528490988128000 := by
  rw [← show ((([(5, 1), (7, 1), (11, 2), (11821, 1), (32479, 1), (42899996362495871, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_7, prime_fiftyNineBE_11, prime_fiftyNineBE_11821, prime_fiftyNineBE_32479, prime_fiftyNineBE_42899996362495871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334416 : Nat.totient 69753746162066514183170334416 = 34876873081033257091585167200 := by
  rw [← show ((([(2, 4), (4359609135129157136448145901, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_4359609135129157136448145901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334417 : Nat.totient 69753746162066514183170334417 = 44896014140958907884760366080 := by
  rw [← show ((([(3, 1), (31, 1), (433, 1), (22397, 1), (96263, 1), (803428899812863, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_31, prime_fiftyNineBE_433, prime_fiftyNineBE_22397, prime_fiftyNineBE_96263, prime_fiftyNineBE_803428899812863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334418 : Nat.totient 69753746162066514183170334418 = 34876873081032740428321967700 := by
  rw [← show ((([(2, 1), (79842531641359, 1), (436820731558151, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_79842531641359, prime_fiftyNineBE_436820731558151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334419 : Nat.totient 69753746162066514183170334419 = 69753386757496745186381232000 := by
  rw [← show ((([(194101, 1), (1923137809, 1), (186865599075191, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_194101, prime_fiftyNineBE_1923137809, prime_fiftyNineBE_186865599075191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334420 : Nat.totient 69753746162066514183170334420 = 17616459262636607811568128000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (3181, 1), (25421823013, 1), (756645276601, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_19, prime_fiftyNineBE_3181, prime_fiftyNineBE_25421823013, prime_fiftyNineBE_756645276601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334421 : Nat.totient 69753746162066514183170334421 = 67348444568633575618049822400 := by
  rw [← show ((([(29, 1), (41127807101, 1), (58483584740819149, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_29, prime_fiftyNineBE_41127807101, prime_fiftyNineBE_58483584740819149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334422 : Nat.totient 69753746162066514183170334422 = 28091373179967887847592550400 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (631, 1), (12922561, 1), (35942859843273659, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_7, prime_fiftyNineBE_17, prime_fiftyNineBE_631, prime_fiftyNineBE_12922561, prime_fiftyNineBE_35942859843273659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334423 : Nat.totient 69753746162066514183170334423 = 42860245007096921361207684672 := by
  rw [← show ((([(3, 2), (13, 1), (659, 1), (447066107, 1), (2023599269167163, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_13, prime_fiftyNineBE_659, prime_fiftyNineBE_447066107, prime_fiftyNineBE_2023599269167163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334424 : Nat.totient 69753746162066514183170334424 = 34531557499229794382212848000 := by
  rw [← show ((([(2, 3), (101, 1), (5120546173, 1), (16859313606063211, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_101, prime_fiftyNineBE_5120546173, prime_fiftyNineBE_16859313606063211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334425 : Nat.totient 69753746162066514183170334425 = 55788475663933970593264554240 := by
  rw [← show ((([(5, 2), (3853, 1), (1667629, 1), (11596087, 1), (37447050383, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_3853, prime_fiftyNineBE_1667629, prime_fiftyNineBE_11596087, prime_fiftyNineBE_37447050383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334426 : Nat.totient 69753746162066514183170334426 = 20645928284418733821998390400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (25420511, 1), (966876197719064057, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_11, prime_fiftyNineBE_43, prime_fiftyNineBE_25420511, prime_fiftyNineBE_966876197719064057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334427 : Nat.totient 69753746162066514183170334427 = 66720974589799363438155652992 := by
  rw [← show ((([(23, 1), (23171065185137, 1), (130886152536877, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_23, prime_fiftyNineBE_23171065185137, prime_fiftyNineBE_130886152536877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334428 : Nat.totient 69753746162066514183170334428 = 34465087288680800835070310400 := by
  rw [← show ((([(2, 2), (109, 1), (419, 1), (5563, 1), (11593, 1), (203351, 1), (29114934413, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_109, prime_fiftyNineBE_419, prime_fiftyNineBE_5563, prime_fiftyNineBE_11593, prime_fiftyNineBE_203351, prime_fiftyNineBE_29114934413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334429 : Nat.totient 69753746162066514183170334429 = 39846792363700081522910534640 := by
  rw [← show ((([(3, 1), (7, 1), (3191, 1), (1040929790065310384611039, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_7, prime_fiftyNineBE_3191, prime_fiftyNineBE_1040929790065310384611039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334430 : Nat.totient 69753746162066514183170334430 = 27900621809140554347371977600 := by
  rw [← show ((([(2, 1), (5, 1), (34519, 1), (471061, 1), (3055231, 1), (140406795967, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_34519, prime_fiftyNineBE_471061, prime_fiftyNineBE_3055231, prime_fiftyNineBE_140406795967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334431 : Nat.totient 69753746162066514183170334431 = 69603223777423832540313325056 := by
  rw [← show ((([(467, 1), (63337, 1), (1204037, 1), (1958634202977497, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_467, prime_fiftyNineBE_63337, prime_fiftyNineBE_1204037, prime_fiftyNineBE_1958634202977497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334432 : Nat.totient 69753746162066514183170334432 = 23251248502762469855961772800 := by
  rw [← show ((([(2, 5), (3, 4), (106693141, 1), (252229592723277931, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_106693141, prime_fiftyNineBE_252229592723277931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334433 : Nat.totient 69753746162066514183170334433 = 69753746162066514183170334432 := by
  rw [← show ((([(69753746162066514183170334433, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_69753746162066514183170334433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334434 : Nat.totient 69753746162066514183170334434 = 34876873081033257091585167216 := by
  rw [← show ((([(2, 1), (34876873081033257091585167217, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_34876873081033257091585167217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334435 : Nat.totient 69753746162066514183170334435 = 37200725263219718054103402720 := by
  rw [← show ((([(3, 1), (5, 1), (29231, 1), (159086235302855448401059, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_29231, prime_fiftyNineBE_159086235302855448401059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334436 : Nat.totient 69753746162066514183170334436 = 27070336419091333043149393920 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 1), (7129, 1), (281581, 1), (1801185000486467, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_7, prime_fiftyNineBE_13, prime_fiftyNineBE_53, prime_fiftyNineBE_7129, prime_fiftyNineBE_281581, prime_fiftyNineBE_1801185000486467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334437 : Nat.totient 69753746162066514183170334437 = 63412496510966195342383087360 := by
  rw [← show ((([(11, 1), (20051435568449, 1), (316249159789583, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_11, prime_fiftyNineBE_20051435568449, prime_fiftyNineBE_316249159789583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334438 : Nat.totient 69753746162066514183170334438 = 23251180806744044149436905728 := by
  rw [← show ((([(2, 1), (3, 1), (342373, 1), (12257855413, 1), (2770143604777, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_342373, prime_fiftyNineBE_12257855413, prime_fiftyNineBE_2770143604777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334439 : Nat.totient 69753746162066514183170334439 = 62184261206194217957883302784 := by
  rw [← show ((([(17, 1), (19, 1), (5639, 1), (38296838175349204035787, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_17, prime_fiftyNineBE_19, prime_fiftyNineBE_5639, prime_fiftyNineBE_38296838175349204035787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334440 : Nat.totient 69753746162066514183170334440 = 27784505230360130319458586624 := by
  rw [← show ((([(2, 3), (5, 1), (373, 1), (773, 1), (4493, 1), (4181347, 1), (321933811079, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_373, prime_fiftyNineBE_773, prime_fiftyNineBE_4493, prime_fiftyNineBE_4181347, prime_fiftyNineBE_321933811079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334441 : Nat.totient 69753746162066514183170334441 = 46136325939121085919500971008 := by
  rw [← show ((([(3, 2), (127, 1), (4583633, 1), (1315544183, 1), (10120594633, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_127, prime_fiftyNineBE_4583633, prime_fiftyNineBE_1315544183, prime_fiftyNineBE_10120594633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334442 : Nat.totient 69753746162066514183170334442 = 34025683836828328903552950880 := by
  rw [← show ((([(2, 1), (41, 1), (63743, 1), (13345080102925986360467, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_41, prime_fiftyNineBE_63743, prime_fiftyNineBE_13345080102925986360467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334443 : Nat.totient 69753746162066514183170334443 = 59784775290428077818683874000 := by
  rw [← show ((([(7, 2), (14407, 1), (98809317695715538199501, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_7, prime_fiftyNineBE_14407, prime_fiftyNineBE_98809317695715538199501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334444 : Nat.totient 69753746162066514183170334444 = 22622836593102653248595784000 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (157103031896546203115248501, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_37, prime_fiftyNineBE_157103031896546203115248501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334445 : Nat.totient 69753746162066514183170334445 = 55781357613444536290961447808 := by
  rw [← show ((([(5, 1), (2579, 1), (29973529, 1), (180471368485863979, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_2579, prime_fiftyNineBE_29973529, prime_fiftyNineBE_180471368485863979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334446 : Nat.totient 69753746162066514183170334446 = 34489657794724790253075020160 := by
  rw [← show ((([(2, 1), (107, 1), (593, 1), (11503, 1), (47784599467265551291, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_107, prime_fiftyNineBE_593, prime_fiftyNineBE_11503, prime_fiftyNineBE_47784599467265551291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334447 : Nat.totient 69753746162066514183170334447 = 46492017940761331853535413472 := by
  rw [← show ((([(3, 1), (4463, 1), (775639, 1), (6716758866059818957, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_4463, prime_fiftyNineBE_775639, prime_fiftyNineBE_6716758866059818957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334448 : Nat.totient 69753746162066514183170334448 = 30597996788378861607803904000 := by
  rw [← show ((([(2, 4), (11, 1), (31, 1), (359, 1), (62601347297, 1), (568872639221, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_11, prime_fiftyNineBE_31, prime_fiftyNineBE_359, prime_fiftyNineBE_62601347297, prime_fiftyNineBE_568872639221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334449 : Nat.totient 69753746162066514183170334449 = 63379260014285633432023893312 := by
  rw [← show ((([(13, 1), (67, 1), (1327, 1), (4186876123, 1), (14414127095339, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_13, prime_fiftyNineBE_67, prime_fiftyNineBE_1327, prime_fiftyNineBE_4186876123, prime_fiftyNineBE_14414127095339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334450 : Nat.totient 69753746162066514183170334450 = 14399523241747357904715571200 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (29, 1), (61, 1), (173, 1), (125202499, 1), (25127091047, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_7, prime_fiftyNineBE_23, prime_fiftyNineBE_29, prime_fiftyNineBE_61, prime_fiftyNineBE_173, prime_fiftyNineBE_125202499, prime_fiftyNineBE_25127091047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334451 : Nat.totient 69753746162066514183170334451 = 68816928739985568452805580800 := by
  rw [← show ((([(89, 1), (461, 1), (35593, 1), (83407, 1), (98411, 1), (5819234579, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_89, prime_fiftyNineBE_461, prime_fiftyNineBE_35593, prime_fiftyNineBE_83407, prime_fiftyNineBE_98411, prime_fiftyNineBE_5819234579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334452 : Nat.totient 69753746162066514183170334452 = 34876873079053930671730634496 := by
  rw [← show ((([(2, 2), (17620577057, 1), (989663192306689309, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_17620577057, prime_fiftyNineBE_989663192306689309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334453 : Nat.totient 69753746162066514183170334453 = 45425221541841051500198136320 := by
  rw [← show ((([(3, 1), (47, 1), (521, 1), (90149, 1), (10532944287843957677, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_47, prime_fiftyNineBE_521, prime_fiftyNineBE_90149, prime_fiftyNineBE_10532944287843957677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334454 : Nat.totient 69753746162066514183170334454 = 34795952261771435606506608000 := by
  rw [← show ((([(2, 1), (431, 1), (725287803217, 1), (111570632864101, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_431, prime_fiftyNineBE_725287803217, prime_fiftyNineBE_111570632864101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334455 : Nat.totient 69753746162066514183170334455 = 55802996929525211926924897600 := by
  rw [← show ((([(5, 1), (435968829971, 1), (31999418934012521, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_435968829971, prime_fiftyNineBE_31999418934012521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334456 : Nat.totient 69753746162066514183170334456 = 21799179188209417816571904000 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (281, 1), (3457, 1), (132911, 1), (1324160865384611, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_17, prime_fiftyNineBE_281, prime_fiftyNineBE_3457, prime_fiftyNineBE_132911, prime_fiftyNineBE_1324160865384611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334457 : Nat.totient 69753746162066514183170334457 = 59332766949961372968275612160 := by
  rw [← show ((([(7, 1), (137, 1), (3359, 1), (28621, 1), (756578720023024957, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_7, prime_fiftyNineBE_137, prime_fiftyNineBE_3359, prime_fiftyNineBE_28621, prime_fiftyNineBE_756578720023024957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334458 : Nat.totient 69753746162066514183170334458 = 33041233434350662073034047280 := by
  rw [← show ((([(2, 1), (19, 1), (2396131, 1), (34480343, 1), (22217838453827, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_19, prime_fiftyNineBE_2396131, prime_fiftyNineBE_34480343, prime_fiftyNineBE_22217838453827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334459 : Nat.totient 69753746162066514183170334459 = 41962635640571342863208232960 := by
  rw [← show ((([(3, 3), (11, 1), (199, 1), (643, 1), (1217, 1), (1508191398886036663, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_11, prime_fiftyNineBE_199, prime_fiftyNineBE_643, prime_fiftyNineBE_1217, prime_fiftyNineBE_1508191398886036663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334460 : Nat.totient 69753746162066514183170334460 = 27862144290290314936795302144 := by
  rw [← show ((([(2, 2), (5, 1), (709, 1), (32316149, 1), (152219995188155803, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_709, prime_fiftyNineBE_32316149, prime_fiftyNineBE_152219995188155803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334461 : Nat.totient 69753746162066514183170334461 = 69753746162066514183170334460 := by
  rw [← show ((([(69753746162066514183170334461, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_69753746162066514183170334461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334462 : Nat.totient 69753746162066514183170334462 = 21098916700651387882429344000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (81023614531, 1), (187072223729401, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_13, prime_fiftyNineBE_59, prime_fiftyNineBE_81023614531, prime_fiftyNineBE_187072223729401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334463 : Nat.totient 69753746162066514183170334463 = 69560741690667325723130021376 := by
  rw [← show ((([(367, 1), (23663, 1), (42015855967, 1), (191169433409, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_367, prime_fiftyNineBE_23663, prime_fiftyNineBE_42015855967, prime_fiftyNineBE_191169433409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334464 : Nat.totient 69753746162066514183170334464 = 29894433898483673169383817216 := by
  rw [← show ((([(2, 8), (7, 1), (1221097, 1), (7016237, 1), (4543338724453, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_7, prime_fiftyNineBE_1221097, prime_fiftyNineBE_7016237, prime_fiftyNineBE_4543338724453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334465 : Nat.totient 69753746162066514183170334465 = 36692381542785673214160832896 := by
  rw [← show ((([(3, 1), (5, 1), (73, 1), (63702051289558460441251447, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_73, prime_fiftyNineBE_63702051289558460441251447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334466 : Nat.totient 69753746162066514183170334466 = 34840276152301847587816451520 := by
  rw [← show ((([(2, 1), (953, 1), (36596928731409503768714761, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_953, prime_fiftyNineBE_36596928731409503768714761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334467 : Nat.totient 69753746162066514183170334467 = 69749771397432957655967600640 := by
  rw [← show ((([(31699, 1), (39313, 1), (55973928455542464641, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_31699, prime_fiftyNineBE_39313, prime_fiftyNineBE_55973928455542464641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334468 : Nat.totient 69753746162066514183170334468 = 23237547336646004332087366656 := by
  rw [← show ((([(2, 2), (3, 2), (1697, 1), (1141782003569477414115929, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_1697, prime_fiftyNineBE_1141782003569477414115929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334469 : Nat.totient 69753746162066514183170334469 = 68095057475451173048294890176 := by
  rw [← show ((([(43, 1), (1933, 1), (53959, 1), (15552611891457397789, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_43, prime_fiftyNineBE_1933, prime_fiftyNineBE_53959, prime_fiftyNineBE_15552611891457397789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334470 : Nat.totient 69753746162066514183170334470 = 25364998604387823339334667040 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (634124965109695583483366677, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_11, prime_fiftyNineBE_634124965109695583483366677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334471 : Nat.totient 69753746162066514183170334471 = 39859261260712622762663646720 := by
  rw [← show ((([(3, 1), (7, 1), (1818617, 1), (116171963, 1), (15721923094681, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_7, prime_fiftyNineBE_1818617, prime_fiftyNineBE_116171963, prime_fiftyNineBE_15721923094681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334472 : Nat.totient 69753746162066514183170334472 = 34770900414574372484414313280 := by
  rw [← show ((([(2, 3), (383, 1), (2333, 1), (9758072417945175613931, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_383, prime_fiftyNineBE_2333, prime_fiftyNineBE_9758072417945175613931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334473 : Nat.totient 69753746162066514183170334473 = 62796211378637884891242858304 := by
  rw [← show ((([(17, 1), (23, 1), (178398327780221263895576303, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_17, prime_fiftyNineBE_23, prime_fiftyNineBE_178398327780221263895576303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334474 : Nat.totient 69753746162066514183170334474 = 23238873769961125618532751792 := by
  rw [← show ((([(2, 1), (3, 1), (1879, 1), (34015703, 1), (181890516079204967, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_1879, prime_fiftyNineBE_34015703, prime_fiftyNineBE_181890516079204967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334475 : Nat.totient 69753746162066514183170334475 = 50460644599654086523035648000 := by
  rw [← show ((([(5, 2), (13, 1), (83, 1), (193, 1), (313, 1), (13339, 1), (3209084583180551, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_13, prime_fiftyNineBE_83, prime_fiftyNineBE_193, prime_fiftyNineBE_313, prime_fiftyNineBE_13339, prime_fiftyNineBE_3209084583180551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334476 : Nat.totient 69753746162066514183170334476 = 34872715624348303248032276544 := by
  rw [← show ((([(2, 2), (8389, 1), (9422502709, 1), (220612989573419, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_8389, prime_fiftyNineBE_9422502709, prime_fiftyNineBE_220612989573419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334477 : Nat.totient 69753746162066514183170334477 = 43642746858824490212292796416 := by
  rw [← show ((([(3, 2), (19, 1), (113, 1), (2069, 1), (34123, 1), (51131117654751377, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_19, prime_fiftyNineBE_113, prime_fiftyNineBE_2069, prime_fiftyNineBE_34123, prime_fiftyNineBE_51131117654751377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334478 : Nat.totient 69753746162066514183170334478 = 29893934572795686107767251960 := by
  rw [← show ((([(2, 1), (7, 1), (56611, 1), (88011348327137979472907, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_7, prime_fiftyNineBE_56611, prime_fiftyNineBE_88011348327137979472907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334479 : Nat.totient 69753746162066514183170334479 = 65147164248431642547892925280 := by
  rw [← show ((([(29, 1), (31, 1), (2267, 1), (34226014084201047864863, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_29, prime_fiftyNineBE_31, prime_fiftyNineBE_2267, prime_fiftyNineBE_34226014084201047864863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334480 : Nat.totient 69753746162066514183170334480 = 18317185488535580240128819200 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (71, 1), (967, 1), (7757, 1), (36563, 1), (14925739520521, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_71, prime_fiftyNineBE_967, prime_fiftyNineBE_7757, prime_fiftyNineBE_36563, prime_fiftyNineBE_14925739520521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334481 : Nat.totient 69753746162066514183170334481 = 61582494313966457952755712000 := by
  rw [← show ((([(11, 1), (37, 1), (571, 1), (8641, 1), (90007, 1), (215843, 1), (1787963953, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_11, prime_fiftyNineBE_37, prime_fiftyNineBE_571, prime_fiftyNineBE_8641, prime_fiftyNineBE_90007, prime_fiftyNineBE_215843, prime_fiftyNineBE_1787963953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334482 : Nat.totient 69753746162066514183170334482 = 34435040425123360324169088000 := by
  rw [← show ((([(2, 1), (79, 1), (121321, 1), (502861, 1), (49160569, 1), (147200611, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_79, prime_fiftyNineBE_121321, prime_fiftyNineBE_502861, prime_fiftyNineBE_49160569, prime_fiftyNineBE_147200611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334483 : Nat.totient 69753746162066514183170334483 = 45364701947907137006858250240 := by
  rw [← show ((([(3, 1), (41, 1), (13033, 1), (426707, 1), (52151069, 1), (1955352439, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_41, prime_fiftyNineBE_13033, prime_fiftyNineBE_426707, prime_fiftyNineBE_52151069, prime_fiftyNineBE_1955352439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334484 : Nat.totient 69753746162066514183170334484 = 34649861143001701066837855488 := by
  rw [← show ((([(2, 2), (157, 1), (7127, 1), (9134903, 1), (1706071365737113, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_157, prime_fiftyNineBE_7127, prime_fiftyNineBE_9134903, prime_fiftyNineBE_1706071365737113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334485 : Nat.totient 69753746162066514183170334485 = 47830621466372046083778794688 := by
  rw [← show ((([(5, 1), (7, 1), (92203, 1), (21614960208008885419957, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_5, prime_fiftyNineBE_7, prime_fiftyNineBE_92203, prime_fiftyNineBE_21614960208008885419957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334486 : Nat.totient 69753746162066514183170334486 = 23248172750247328303754258400 := by
  rw [← show ((([(2, 1), (3, 3), (7559, 1), (14853086021, 1), (11505161919931, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_7559, prime_fiftyNineBE_14853086021, prime_fiftyNineBE_11505161919931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334487 : Nat.totient 69753746162066514183170334487 = 69753746162066514183170334486 := by
  rw [← show ((([(69753746162066514183170334487, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_69753746162066514183170334487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334488 : Nat.totient 69753746162066514183170334488 = 32194035480960759563855535360 := by
  rw [← show ((([(2, 3), (13, 1), (26623721, 1), (25192162196718408407, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_13, prime_fiftyNineBE_26623721, prime_fiftyNineBE_25192162196718408407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334489 : Nat.totient 69753746162066514183170334489 = 45625089160179281396748748800 := by
  rw [← show ((([(3, 1), (53, 1), (17093831, 1), (25664393549388243841, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_53, prime_fiftyNineBE_17093831, prime_fiftyNineBE_25664393549388243841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334490 : Nat.totient 69753746162066514183170334490 = 26260233849248570045428831744 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (410316153894508906959825497, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_17, prime_fiftyNineBE_410316153894508906959825497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334491 : Nat.totient 69753746162066514183170334491 = 69730261244253306185865330240 := by
  rw [← show ((([(2971, 1), (11803663, 1), (86885129, 1), (22892996023, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2971, prime_fiftyNineBE_11803663, prime_fiftyNineBE_86885129, prime_fiftyNineBE_22892996023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334492 : Nat.totient 69753746162066514183170334492 = 17928315710005433823467274240 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (11, 1), (97, 1), (6653, 1), (283553, 1), (58935099508003, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_7, prime_fiftyNineBE_11, prime_fiftyNineBE_97, prime_fiftyNineBE_6653, prime_fiftyNineBE_283553, prime_fiftyNineBE_58935099508003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334493 : Nat.totient 69753746162066514183170334493 = 69215736502708048475368372800 := by
  rw [← show ((([(197, 1), (379, 1), (151847, 1), (191563, 1), (32117686496551, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_197, prime_fiftyNineBE_379, prime_fiftyNineBE_151847, prime_fiftyNineBE_191563, prime_fiftyNineBE_32117686496551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334494 : Nat.totient 69753746162066514183170334494 = 34748176132388086143148730520 := by
  rw [← show ((([(2, 1), (271, 1), (7460811921859, 1), (17249724290923, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_271, prime_fiftyNineBE_7460811921859, prime_fiftyNineBE_17249724290923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334495 : Nat.totient 69753746162066514183170334495 = 37166297105753878489692361920 := by
  rw [← show ((([(3, 2), (5, 1), (1091, 1), (23203, 1), (61233083858625954307, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_3, prime_fiftyNineBE_5, prime_fiftyNineBE_1091, prime_fiftyNineBE_23203, prime_fiftyNineBE_61233083858625954307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334496 : Nat.totient 69753746162066514183170334496 = 31604672174117093382763669248 := by
  rw [← show ((([(2, 5), (19, 1), (23, 1), (4988111138591712970764469, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_19, prime_fiftyNineBE_23, prime_fiftyNineBE_4988111138591712970764469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334497 : Nat.totient 69753746162066514183170334497 = 68778431158941409892402011392 := by
  rw [← show ((([(103, 1), (269, 1), (1669, 1), (982603, 1), (1535124523077253, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_103, prime_fiftyNineBE_269, prime_fiftyNineBE_1669, prime_fiftyNineBE_982603, prime_fiftyNineBE_1535124523077253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334498 : Nat.totient 69753746162066514183170334498 = 23251248720688838061056778164 := by
  rw [← show ((([(2, 1), (3, 1), (11625624360344419030528389083, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_3, prime_fiftyNineBE_11625624360344419030528389083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334499 : Nat.totient 69753746162066514183170334499 = 59788903675623758353408392000 := by
  rw [← show ((([(7, 1), (2915327, 1), (54469091, 1), (62752653409801, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_7, prime_fiftyNineBE_2915327, prime_fiftyNineBE_54469091, prime_fiftyNineBE_62752653409801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyNineBE_69753746162066514183170334500 : Nat.totient 69753746162066514183170334500 = 27301118136121704700326758400 := by
  rw [← show ((([(2, 2), (5, 3), (47, 1), (4057, 1), (71807977, 1), (10188775071443, 1)] : List FactorBlock).map factorBlockValue).prod) = 69753746162066514183170334500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyNineBE_2, prime_fiftyNineBE_5, prime_fiftyNineBE_47, prime_fiftyNineBE_4057, prime_fiftyNineBE_71807977, prime_fiftyNineBE_10188775071443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyNineBE : certifiedKill 1 69753746162066514183170334399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyNineBE_69753746162066514183170334400, phi_fiftyNineBE_69753746162066514183170334401, phi_fiftyNineBE_69753746162066514183170334402,
    phi_fiftyNineBE_69753746162066514183170334403, phi_fiftyNineBE_69753746162066514183170334404, phi_fiftyNineBE_69753746162066514183170334405,
    phi_fiftyNineBE_69753746162066514183170334406, phi_fiftyNineBE_69753746162066514183170334407, phi_fiftyNineBE_69753746162066514183170334408,
    phi_fiftyNineBE_69753746162066514183170334409, phi_fiftyNineBE_69753746162066514183170334410, phi_fiftyNineBE_69753746162066514183170334411,
    phi_fiftyNineBE_69753746162066514183170334412, phi_fiftyNineBE_69753746162066514183170334413, phi_fiftyNineBE_69753746162066514183170334414,
    phi_fiftyNineBE_69753746162066514183170334415, phi_fiftyNineBE_69753746162066514183170334416, phi_fiftyNineBE_69753746162066514183170334417,
    phi_fiftyNineBE_69753746162066514183170334418, phi_fiftyNineBE_69753746162066514183170334419, phi_fiftyNineBE_69753746162066514183170334420,
    phi_fiftyNineBE_69753746162066514183170334421, phi_fiftyNineBE_69753746162066514183170334422, phi_fiftyNineBE_69753746162066514183170334423,
    phi_fiftyNineBE_69753746162066514183170334424, phi_fiftyNineBE_69753746162066514183170334425, phi_fiftyNineBE_69753746162066514183170334426,
    phi_fiftyNineBE_69753746162066514183170334427, phi_fiftyNineBE_69753746162066514183170334428, phi_fiftyNineBE_69753746162066514183170334429,
    phi_fiftyNineBE_69753746162066514183170334430, phi_fiftyNineBE_69753746162066514183170334431, phi_fiftyNineBE_69753746162066514183170334432,
    phi_fiftyNineBE_69753746162066514183170334433, phi_fiftyNineBE_69753746162066514183170334434, phi_fiftyNineBE_69753746162066514183170334435,
    phi_fiftyNineBE_69753746162066514183170334436, phi_fiftyNineBE_69753746162066514183170334437, phi_fiftyNineBE_69753746162066514183170334438,
    phi_fiftyNineBE_69753746162066514183170334439, phi_fiftyNineBE_69753746162066514183170334440, phi_fiftyNineBE_69753746162066514183170334441,
    phi_fiftyNineBE_69753746162066514183170334442, phi_fiftyNineBE_69753746162066514183170334443, phi_fiftyNineBE_69753746162066514183170334444,
    phi_fiftyNineBE_69753746162066514183170334445, phi_fiftyNineBE_69753746162066514183170334446, phi_fiftyNineBE_69753746162066514183170334447,
    phi_fiftyNineBE_69753746162066514183170334448, phi_fiftyNineBE_69753746162066514183170334449, phi_fiftyNineBE_69753746162066514183170334450,
    phi_fiftyNineBE_69753746162066514183170334451, phi_fiftyNineBE_69753746162066514183170334452, phi_fiftyNineBE_69753746162066514183170334453,
    phi_fiftyNineBE_69753746162066514183170334454, phi_fiftyNineBE_69753746162066514183170334455, phi_fiftyNineBE_69753746162066514183170334456,
    phi_fiftyNineBE_69753746162066514183170334457, phi_fiftyNineBE_69753746162066514183170334458, phi_fiftyNineBE_69753746162066514183170334459,
    phi_fiftyNineBE_69753746162066514183170334460, phi_fiftyNineBE_69753746162066514183170334461, phi_fiftyNineBE_69753746162066514183170334462,
    phi_fiftyNineBE_69753746162066514183170334463, phi_fiftyNineBE_69753746162066514183170334464, phi_fiftyNineBE_69753746162066514183170334465,
    phi_fiftyNineBE_69753746162066514183170334466, phi_fiftyNineBE_69753746162066514183170334467, phi_fiftyNineBE_69753746162066514183170334468,
    phi_fiftyNineBE_69753746162066514183170334469, phi_fiftyNineBE_69753746162066514183170334470, phi_fiftyNineBE_69753746162066514183170334471,
    phi_fiftyNineBE_69753746162066514183170334472, phi_fiftyNineBE_69753746162066514183170334473, phi_fiftyNineBE_69753746162066514183170334474,
    phi_fiftyNineBE_69753746162066514183170334475, phi_fiftyNineBE_69753746162066514183170334476, phi_fiftyNineBE_69753746162066514183170334477,
    phi_fiftyNineBE_69753746162066514183170334478, phi_fiftyNineBE_69753746162066514183170334479, phi_fiftyNineBE_69753746162066514183170334480,
    phi_fiftyNineBE_69753746162066514183170334481, phi_fiftyNineBE_69753746162066514183170334482, phi_fiftyNineBE_69753746162066514183170334483,
    phi_fiftyNineBE_69753746162066514183170334484, phi_fiftyNineBE_69753746162066514183170334485, phi_fiftyNineBE_69753746162066514183170334486,
    phi_fiftyNineBE_69753746162066514183170334487, phi_fiftyNineBE_69753746162066514183170334488, phi_fiftyNineBE_69753746162066514183170334489,
    phi_fiftyNineBE_69753746162066514183170334490, phi_fiftyNineBE_69753746162066514183170334491, phi_fiftyNineBE_69753746162066514183170334492,
    phi_fiftyNineBE_69753746162066514183170334493, phi_fiftyNineBE_69753746162066514183170334494, phi_fiftyNineBE_69753746162066514183170334495,
    phi_fiftyNineBE_69753746162066514183170334496, phi_fiftyNineBE_69753746162066514183170334497, phi_fiftyNineBE_69753746162066514183170334498,
    phi_fiftyNineBE_69753746162066514183170334499, phi_fiftyNineBE_69753746162066514183170334500]

end TotientTailPeriodKiller
end Erdos249257
