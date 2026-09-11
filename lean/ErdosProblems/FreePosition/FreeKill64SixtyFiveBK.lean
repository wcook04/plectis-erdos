import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 65P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyFiveBKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyFiveBKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyFiveBKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyFiveBKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyFiveBKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyFiveBKFastPow a n * sixtyFiveBKFastPow a n * a
        else sixtyFiveBKFastPow a n * sixtyFiveBKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyFiveBK_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyFiveBK_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyFiveBK_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyFiveBK_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyFiveBK_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyFiveBK_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyFiveBK_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyFiveBK_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyFiveBK_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyFiveBK_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyFiveBK_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyFiveBK_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyFiveBK_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyFiveBK_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyFiveBK_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyFiveBK_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyFiveBK_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyFiveBK_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyFiveBK_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyFiveBK_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyFiveBK_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyFiveBK_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyFiveBK_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyFiveBK_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyFiveBK_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyFiveBK_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyFiveBK_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyFiveBK_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyFiveBK_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyFiveBK_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyFiveBK_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyFiveBK_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyFiveBK_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyFiveBK_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyFiveBK_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyFiveBK_151 : Nat.Prime 151 := by norm_num
private theorem prime_sixtyFiveBK_157 : Nat.Prime 157 := by norm_num
private theorem prime_sixtyFiveBK_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyFiveBK_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyFiveBK_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyFiveBK_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyFiveBK_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyFiveBK_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyFiveBK_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtyFiveBK_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyFiveBK_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyFiveBK_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyFiveBK_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyFiveBK_241 : Nat.Prime 241 := by norm_num
private theorem prime_sixtyFiveBK_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyFiveBK_257 : Nat.Prime 257 := by norm_num
private theorem prime_sixtyFiveBK_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyFiveBK_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyFiveBK_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyFiveBK_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtyFiveBK_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyFiveBK_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyFiveBK_293 : Nat.Prime 293 := by norm_num
private theorem prime_sixtyFiveBK_307 : Nat.Prime 307 := by norm_num
private theorem prime_sixtyFiveBK_311 : Nat.Prime 311 := by norm_num
private theorem prime_sixtyFiveBK_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyFiveBK_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtyFiveBK_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyFiveBK_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtyFiveBK_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyFiveBK_349 : Nat.Prime 349 := by norm_num
private theorem prime_sixtyFiveBK_353 : Nat.Prime 353 := by norm_num
private theorem prime_sixtyFiveBK_359 : Nat.Prime 359 := by norm_num
private theorem prime_sixtyFiveBK_367 : Nat.Prime 367 := by norm_num
private theorem prime_sixtyFiveBK_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixtyFiveBK_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyFiveBK_383 : Nat.Prime 383 := by norm_num
private theorem prime_sixtyFiveBK_389 : Nat.Prime 389 := by norm_num
private theorem prime_sixtyFiveBK_401 : Nat.Prime 401 := by norm_num
private theorem prime_sixtyFiveBK_409 : Nat.Prime 409 := by norm_num
private theorem prime_sixtyFiveBK_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyFiveBK_431 : Nat.Prime 431 := by norm_num
private theorem prime_sixtyFiveBK_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyFiveBK_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtyFiveBK_491 : Nat.Prime 491 := by norm_num
private theorem prime_sixtyFiveBK_509 : Nat.Prime 509 := by norm_num
private theorem prime_sixtyFiveBK_521 : Nat.Prime 521 := by norm_num
private theorem prime_sixtyFiveBK_523 : Nat.Prime 523 := by norm_num
private theorem prime_sixtyFiveBK_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyFiveBK_547 : Nat.Prime 547 := by norm_num
private theorem prime_sixtyFiveBK_557 : Nat.Prime 557 := by norm_num
private theorem prime_sixtyFiveBK_563 : Nat.Prime 563 := by norm_num
private theorem prime_sixtyFiveBK_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtyFiveBK_593 : Nat.Prime 593 := by norm_num
private theorem prime_sixtyFiveBK_607 : Nat.Prime 607 := by norm_num
private theorem prime_sixtyFiveBK_619 : Nat.Prime 619 := by norm_num
private theorem prime_sixtyFiveBK_631 : Nat.Prime 631 := by norm_num
private theorem prime_sixtyFiveBK_641 : Nat.Prime 641 := by norm_num
private theorem prime_sixtyFiveBK_647 : Nat.Prime 647 := by norm_num
private theorem prime_sixtyFiveBK_691 : Nat.Prime 691 := by norm_num
private theorem prime_sixtyFiveBK_719 : Nat.Prime 719 := by norm_num
private theorem prime_sixtyFiveBK_733 : Nat.Prime 733 := by norm_num
private theorem prime_sixtyFiveBK_739 : Nat.Prime 739 := by norm_num
private theorem prime_sixtyFiveBK_757 : Nat.Prime 757 := by norm_num
private theorem prime_sixtyFiveBK_761 : Nat.Prime 761 := by norm_num
private theorem prime_sixtyFiveBK_769 : Nat.Prime 769 := by norm_num
private theorem prime_sixtyFiveBK_773 : Nat.Prime 773 := by norm_num
private theorem prime_sixtyFiveBK_797 : Nat.Prime 797 := by norm_num
private theorem prime_sixtyFiveBK_823 : Nat.Prime 823 := by norm_num
private theorem prime_sixtyFiveBK_827 : Nat.Prime 827 := by norm_num
private theorem prime_sixtyFiveBK_859 : Nat.Prime 859 := by norm_num
private theorem prime_sixtyFiveBK_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixtyFiveBK_887 : Nat.Prime 887 := by norm_num
private theorem prime_sixtyFiveBK_907 : Nat.Prime 907 := by norm_num
private theorem prime_sixtyFiveBK_941 : Nat.Prime 941 := by norm_num
private theorem prime_sixtyFiveBK_947 : Nat.Prime 947 := by norm_num
private theorem prime_sixtyFiveBK_967 : Nat.Prime 967 := by norm_num
private theorem prime_sixtyFiveBK_971 : Nat.Prime 971 := by norm_num
private theorem prime_sixtyFiveBK_983 : Nat.Prime 983 := by norm_num
private theorem prime_sixtyFiveBK_991 : Nat.Prime 991 := by norm_num
private theorem prime_sixtyFiveBK_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_sixtyFiveBK_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyFiveBK_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_sixtyFiveBK_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_sixtyFiveBK_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtyFiveBK_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_sixtyFiveBK_1129 : Nat.Prime 1129 := by norm_num
private theorem prime_sixtyFiveBK_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_sixtyFiveBK_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_sixtyFiveBK_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_sixtyFiveBK_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_sixtyFiveBK_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_sixtyFiveBK_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_sixtyFiveBK_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_sixtyFiveBK_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_sixtyFiveBK_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_sixtyFiveBK_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_sixtyFiveBK_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_sixtyFiveBK_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_sixtyFiveBK_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_sixtyFiveBK_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_sixtyFiveBK_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_sixtyFiveBK_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_sixtyFiveBK_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_sixtyFiveBK_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_sixtyFiveBK_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_sixtyFiveBK_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_sixtyFiveBK_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_sixtyFiveBK_1931 : Nat.Prime 1931 := by norm_num
private theorem prime_sixtyFiveBK_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_sixtyFiveBK_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_sixtyFiveBK_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_sixtyFiveBK_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_sixtyFiveBK_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_sixtyFiveBK_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_sixtyFiveBK_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_sixtyFiveBK_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_sixtyFiveBK_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_sixtyFiveBK_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_sixtyFiveBK_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_sixtyFiveBK_2741 : Nat.Prime 2741 := by norm_num
private theorem prime_sixtyFiveBK_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_sixtyFiveBK_2789 : Nat.Prime 2789 := by norm_num
private theorem prime_sixtyFiveBK_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_sixtyFiveBK_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_sixtyFiveBK_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_sixtyFiveBK_3049 : Nat.Prime 3049 := by norm_num
private theorem prime_sixtyFiveBK_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_sixtyFiveBK_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_sixtyFiveBK_3313 : Nat.Prime 3313 := by norm_num
private theorem prime_sixtyFiveBK_3347 : Nat.Prime 3347 := by norm_num
private theorem prime_sixtyFiveBK_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_sixtyFiveBK_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_sixtyFiveBK_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_sixtyFiveBK_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_sixtyFiveBK_3557 : Nat.Prime 3557 := by norm_num
private theorem prime_sixtyFiveBK_3613 : Nat.Prime 3613 := by norm_num
private theorem prime_sixtyFiveBK_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_sixtyFiveBK_3659 : Nat.Prime 3659 := by norm_num
private theorem prime_sixtyFiveBK_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_sixtyFiveBK_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_sixtyFiveBK_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_sixtyFiveBK_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_sixtyFiveBK_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_sixtyFiveBK_4337 : Nat.Prime 4337 := by norm_num
private theorem prime_sixtyFiveBK_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_sixtyFiveBK_4793 : Nat.Prime 4793 := by norm_num
private theorem prime_sixtyFiveBK_4951 : Nat.Prime 4951 := by norm_num
private theorem prime_sixtyFiveBK_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_sixtyFiveBK_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_sixtyFiveBK_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_sixtyFiveBK_5407 : Nat.Prime 5407 := by norm_num
private theorem prime_sixtyFiveBK_5623 : Nat.Prime 5623 := by norm_num
private theorem prime_sixtyFiveBK_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_sixtyFiveBK_5851 : Nat.Prime 5851 := by norm_num
private theorem prime_sixtyFiveBK_5867 : Nat.Prime 5867 := by norm_num
private theorem prime_sixtyFiveBK_5903 : Nat.Prime 5903 := by norm_num
private theorem prime_sixtyFiveBK_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_sixtyFiveBK_6029 : Nat.Prime 6029 := by norm_num
private theorem prime_sixtyFiveBK_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_sixtyFiveBK_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_sixtyFiveBK_6091 : Nat.Prime 6091 := by norm_num
private theorem prime_sixtyFiveBK_6277 : Nat.Prime 6277 := by norm_num
private theorem prime_sixtyFiveBK_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_sixtyFiveBK_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_sixtyFiveBK_6719 : Nat.Prime 6719 := by norm_num
private theorem prime_sixtyFiveBK_6781 : Nat.Prime 6781 := by norm_num
private theorem prime_sixtyFiveBK_6871 : Nat.Prime 6871 := by norm_num
private theorem prime_sixtyFiveBK_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_sixtyFiveBK_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_sixtyFiveBK_7753 : Nat.Prime 7753 := by norm_num
private theorem prime_sixtyFiveBK_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_sixtyFiveBK_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_sixtyFiveBK_8093 : Nat.Prime 8093 := by norm_num
private theorem prime_sixtyFiveBK_8191 : Nat.Prime 8191 := by norm_num
private theorem prime_sixtyFiveBK_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_sixtyFiveBK_8243 : Nat.Prime 8243 := by norm_num
private theorem prime_sixtyFiveBK_8447 : Nat.Prime 8447 := by norm_num
private theorem prime_sixtyFiveBK_9227 : Nat.Prime 9227 := by norm_num
private theorem prime_sixtyFiveBK_9337 : Nat.Prime 9337 := by norm_num
private theorem prime_sixtyFiveBK_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_sixtyFiveBK_9619 : Nat.Prime 9619 := by norm_num
private theorem prime_sixtyFiveBK_9791 : Nat.Prime 9791 := by norm_num
private theorem prime_sixtyFiveBK_10193 : Nat.Prime 10193 := by norm_num
private theorem prime_sixtyFiveBK_10223 : Nat.Prime 10223 := by norm_num
private theorem prime_sixtyFiveBK_10247 : Nat.Prime 10247 := by norm_num
private theorem prime_sixtyFiveBK_10271 : Nat.Prime 10271 := by norm_num
private theorem prime_sixtyFiveBK_10313 : Nat.Prime 10313 := by norm_num
private theorem prime_sixtyFiveBK_10853 : Nat.Prime 10853 := by norm_num
private theorem prime_sixtyFiveBK_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_sixtyFiveBK_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_sixtyFiveBK_11689 : Nat.Prime 11689 := by norm_num
private theorem prime_sixtyFiveBK_11813 : Nat.Prime 11813 := by norm_num
private theorem prime_sixtyFiveBK_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_sixtyFiveBK_11831 : Nat.Prime 11831 := by norm_num
private theorem prime_sixtyFiveBK_12473 : Nat.Prime 12473 := by norm_num
private theorem prime_sixtyFiveBK_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_sixtyFiveBK_13469 : Nat.Prime 13469 := by norm_num
private theorem prime_sixtyFiveBK_13781 : Nat.Prime 13781 := by norm_num
private theorem prime_sixtyFiveBK_14591 : Nat.Prime 14591 := by norm_num
private theorem prime_sixtyFiveBK_14929 : Nat.Prime 14929 := by norm_num
private theorem prime_sixtyFiveBK_15017 : Nat.Prime 15017 := by norm_num
private theorem prime_sixtyFiveBK_15091 : Nat.Prime 15091 := by norm_num
private theorem prime_sixtyFiveBK_15263 : Nat.Prime 15263 := by norm_num
private theorem prime_sixtyFiveBK_16183 : Nat.Prime 16183 := by norm_num
private theorem prime_sixtyFiveBK_16651 : Nat.Prime 16651 := by norm_num
private theorem prime_sixtyFiveBK_17203 : Nat.Prime 17203 := by norm_num
private theorem prime_sixtyFiveBK_17957 : Nat.Prime 17957 := by norm_num
private theorem prime_sixtyFiveBK_18539 : Nat.Prime 18539 := by norm_num
private theorem prime_sixtyFiveBK_18839 : Nat.Prime 18839 := by norm_num
private theorem prime_sixtyFiveBK_19219 : Nat.Prime 19219 := by norm_num
private theorem prime_sixtyFiveBK_19231 : Nat.Prime 19231 := by norm_num
private theorem prime_sixtyFiveBK_19541 : Nat.Prime 19541 := by norm_num
private theorem prime_sixtyFiveBK_19891 : Nat.Prime 19891 := by norm_num
private theorem prime_sixtyFiveBK_19937 : Nat.Prime 19937 := by norm_num
private theorem prime_sixtyFiveBK_22259 : Nat.Prime 22259 := by norm_num
private theorem prime_sixtyFiveBK_23773 : Nat.Prime 23773 := by norm_num
private theorem prime_sixtyFiveBK_25303 : Nat.Prime 25303 := by norm_num
private theorem prime_sixtyFiveBK_26099 : Nat.Prime 26099 := by norm_num
private theorem prime_sixtyFiveBK_26449 : Nat.Prime 26449 := by norm_num
private theorem prime_sixtyFiveBK_26459 : Nat.Prime 26459 := by norm_num
private theorem prime_sixtyFiveBK_26813 : Nat.Prime 26813 := by norm_num
private theorem prime_sixtyFiveBK_26981 : Nat.Prime 26981 := by norm_num
private theorem prime_sixtyFiveBK_27103 : Nat.Prime 27103 := by norm_num
private theorem prime_sixtyFiveBK_28087 : Nat.Prime 28087 := by norm_num
private theorem prime_sixtyFiveBK_28669 : Nat.Prime 28669 := by norm_num
private theorem prime_sixtyFiveBK_36671 : Nat.Prime 36671 := by norm_num
private theorem prime_sixtyFiveBK_40093 : Nat.Prime 40093 := by norm_num
private theorem prime_sixtyFiveBK_41681 : Nat.Prime 41681 := by norm_num
private theorem prime_sixtyFiveBK_42703 : Nat.Prime 42703 := by norm_num
private theorem prime_sixtyFiveBK_45439 : Nat.Prime 45439 := by norm_num
private theorem prime_sixtyFiveBK_46691 : Nat.Prime 46691 := by norm_num
private theorem prime_sixtyFiveBK_47041 : Nat.Prime 47041 := by norm_num
private theorem prime_sixtyFiveBK_48413 : Nat.Prime 48413 := by norm_num
private theorem prime_sixtyFiveBK_51257 : Nat.Prime 51257 := by norm_num
private theorem prime_sixtyFiveBK_52783 : Nat.Prime 52783 := by norm_num
private theorem prime_sixtyFiveBK_54617 : Nat.Prime 54617 := by norm_num
private theorem prime_sixtyFiveBK_54941 : Nat.Prime 54941 := by norm_num
private theorem prime_sixtyFiveBK_62533 : Nat.Prime 62533 := by norm_num
private theorem prime_sixtyFiveBK_63737 : Nat.Prime 63737 := by norm_num
private theorem prime_sixtyFiveBK_66293 : Nat.Prime 66293 := by norm_num
private theorem prime_sixtyFiveBK_70841 : Nat.Prime 70841 := by norm_num
private theorem prime_sixtyFiveBK_72287 : Nat.Prime 72287 := by norm_num
private theorem prime_sixtyFiveBK_73517 : Nat.Prime 73517 := by norm_num
private theorem prime_sixtyFiveBK_78541 : Nat.Prime 78541 := by norm_num
private theorem prime_sixtyFiveBK_82847 : Nat.Prime 82847 := by norm_num
private theorem prime_sixtyFiveBK_84967 : Nat.Prime 84967 := by norm_num
private theorem prime_sixtyFiveBK_86539 : Nat.Prime 86539 := by norm_num
private theorem prime_sixtyFiveBK_92503 : Nat.Prime 92503 := by norm_num
private theorem prime_sixtyFiveBK_94153 : Nat.Prime 94153 := by norm_num
private theorem prime_sixtyFiveBK_96451 : Nat.Prime 96451 := by norm_num
private theorem prime_sixtyFiveBK_97841 : Nat.Prime 97841 := by norm_num
private theorem prime_sixtyFiveBK_103681 : Nat.Prime 103681 := by norm_num
private theorem prime_sixtyFiveBK_104527 : Nat.Prime 104527 := by norm_num
private theorem prime_sixtyFiveBK_108271 : Nat.Prime 108271 := by norm_num
private theorem prime_sixtyFiveBK_112291 : Nat.Prime 112291 := by norm_num
private theorem prime_sixtyFiveBK_117841 : Nat.Prime 117841 := by norm_num
private theorem prime_sixtyFiveBK_118057 : Nat.Prime 118057 := by norm_num
private theorem prime_sixtyFiveBK_120431 : Nat.Prime 120431 := by norm_num
private theorem prime_sixtyFiveBK_121181 : Nat.Prime 121181 := by norm_num
private theorem prime_sixtyFiveBK_122611 : Nat.Prime 122611 := by norm_num
private theorem prime_sixtyFiveBK_135271 : Nat.Prime 135271 := by norm_num
private theorem prime_sixtyFiveBK_148793 : Nat.Prime 148793 := by norm_num
private theorem prime_sixtyFiveBK_150377 : Nat.Prime 150377 := by norm_num
private theorem prime_sixtyFiveBK_156131 : Nat.Prime 156131 := by norm_num
private theorem prime_sixtyFiveBK_162823 : Nat.Prime 162823 := by norm_num
private theorem prime_sixtyFiveBK_164683 : Nat.Prime 164683 := by norm_num
private theorem prime_sixtyFiveBK_165463 : Nat.Prime 165463 := by norm_num
private theorem prime_sixtyFiveBK_166631 : Nat.Prime 166631 := by norm_num
private theorem prime_sixtyFiveBK_175859 : Nat.Prime 175859 := by norm_num
private theorem prime_sixtyFiveBK_178067 : Nat.Prime 178067 := by norm_num
private theorem prime_sixtyFiveBK_183089 : Nat.Prime 183089 := by norm_num
private theorem prime_sixtyFiveBK_189691 : Nat.Prime 189691 := by norm_num
private theorem prime_sixtyFiveBK_197677 : Nat.Prime 197677 := by norm_num
private theorem prime_sixtyFiveBK_206033 : Nat.Prime 206033 := by norm_num
private theorem prime_sixtyFiveBK_212141 : Nat.Prime 212141 := by norm_num
private theorem prime_sixtyFiveBK_214147 : Nat.Prime 214147 := by norm_num
private theorem prime_sixtyFiveBK_214559 : Nat.Prime 214559 := by norm_num
private theorem prime_sixtyFiveBK_230819 : Nat.Prime 230819 := by norm_num
private theorem prime_sixtyFiveBK_238639 : Nat.Prime 238639 := by norm_num
private theorem prime_sixtyFiveBK_260047 : Nat.Prime 260047 := by norm_num
private theorem prime_sixtyFiveBK_265231 : Nat.Prime 265231 := by norm_num
private theorem prime_sixtyFiveBK_267803 : Nat.Prime 267803 := by norm_num
private theorem prime_sixtyFiveBK_284969 : Nat.Prime 284969 := by norm_num
private theorem prime_sixtyFiveBK_288661 : Nat.Prime 288661 := by norm_num
private theorem prime_sixtyFiveBK_299731 : Nat.Prime 299731 := by norm_num
private theorem prime_sixtyFiveBK_323233 : Nat.Prime 323233 := by norm_num
private theorem prime_sixtyFiveBK_329957 : Nat.Prime 329957 := by norm_num
private theorem prime_sixtyFiveBK_347579 : Nat.Prime 347579 := by norm_num
private theorem prime_sixtyFiveBK_351707 : Nat.Prime 351707 := by norm_num
private theorem prime_sixtyFiveBK_352333 : Nat.Prime 352333 := by norm_num
private theorem prime_sixtyFiveBK_366787 : Nat.Prime 366787 := by norm_num
private theorem prime_sixtyFiveBK_370871 : Nat.Prime 370871 := by norm_num
private theorem prime_sixtyFiveBK_394367 : Nat.Prime 394367 := by norm_num
private theorem prime_sixtyFiveBK_394579 : Nat.Prime 394579 := by norm_num
private theorem prime_sixtyFiveBK_399739 : Nat.Prime 399739 := by norm_num
private theorem prime_sixtyFiveBK_414959 : Nat.Prime 414959 := by norm_num
private theorem prime_sixtyFiveBK_417491 : Nat.Prime 417491 := by norm_num
private theorem prime_sixtyFiveBK_431077 : Nat.Prime 431077 := by norm_num
private theorem prime_sixtyFiveBK_435653 : Nat.Prime 435653 := by norm_num
private theorem prime_sixtyFiveBK_446387 : Nat.Prime 446387 := by norm_num
private theorem prime_sixtyFiveBK_472393 : Nat.Prime 472393 := by norm_num
private theorem prime_sixtyFiveBK_474223 : Nat.Prime 474223 := by norm_num
private theorem prime_sixtyFiveBK_477469 : Nat.Prime 477469 := by norm_num
private theorem prime_sixtyFiveBK_533303 : Nat.Prime 533303 := by norm_num
private theorem prime_sixtyFiveBK_538079 : Nat.Prime 538079 := by norm_num
private theorem prime_sixtyFiveBK_561839 : Nat.Prime 561839 := by norm_num
private theorem prime_sixtyFiveBK_565667 : Nat.Prime 565667 := by norm_num
private theorem prime_sixtyFiveBK_565997 : Nat.Prime 565997 := by norm_num
private theorem prime_sixtyFiveBK_570643 : Nat.Prime 570643 := by norm_num
private theorem prime_sixtyFiveBK_593141 : Nat.Prime 593141 := by norm_num
private theorem prime_sixtyFiveBK_603821 : Nat.Prime 603821 := by norm_num
private theorem prime_sixtyFiveBK_606847 : Nat.Prime 606847 := by norm_num
private theorem prime_sixtyFiveBK_648671 : Nat.Prime 648671 := by norm_num
private theorem prime_sixtyFiveBK_749971 : Nat.Prime 749971 := by norm_num
private theorem prime_sixtyFiveBK_758969 : Nat.Prime 758969 := by norm_num
private theorem prime_sixtyFiveBK_767843 : Nat.Prime 767843 := by norm_num
private theorem prime_sixtyFiveBK_772139 : Nat.Prime 772139 := by norm_num
private theorem prime_sixtyFiveBK_786823 : Nat.Prime 786823 := by norm_num
private theorem prime_sixtyFiveBK_804653 : Nat.Prime 804653 := by norm_num
private theorem prime_sixtyFiveBK_830743 : Nat.Prime 830743 := by norm_num
private theorem prime_sixtyFiveBK_873349 : Nat.Prime 873349 := by norm_num
private theorem prime_sixtyFiveBK_1065847 : Nat.Prime 1065847 := by norm_num
private theorem prime_sixtyFiveBK_1067441 : Nat.Prime 1067441 := by norm_num
private theorem prime_sixtyFiveBK_1146881 : Nat.Prime 1146881 := by norm_num
private theorem prime_sixtyFiveBK_1261823 : Nat.Prime 1261823 := by norm_num
private theorem prime_sixtyFiveBK_1340903 : Nat.Prime 1340903 := by norm_num
private theorem prime_sixtyFiveBK_1437913 : Nat.Prime 1437913 := by norm_num
private theorem prime_sixtyFiveBK_1438279 : Nat.Prime 1438279 := by norm_num
private theorem prime_sixtyFiveBK_1473239 : Nat.Prime 1473239 := by norm_num
private theorem prime_sixtyFiveBK_1500407 : Nat.Prime 1500407 := by norm_num
private theorem prime_sixtyFiveBK_1570633 : Nat.Prime 1570633 := by norm_num
private theorem prime_sixtyFiveBK_1576013 : Nat.Prime 1576013 := by norm_num
private theorem prime_sixtyFiveBK_1600153 : Nat.Prime 1600153 := by norm_num
private theorem prime_sixtyFiveBK_1622953 : Nat.Prime 1622953 := by norm_num
private theorem prime_sixtyFiveBK_1633361 : Nat.Prime 1633361 := by norm_num
private theorem prime_sixtyFiveBK_1672301 : Nat.Prime 1672301 := by norm_num
private theorem prime_sixtyFiveBK_1895207 : Nat.Prime 1895207 := by norm_num
private theorem prime_sixtyFiveBK_2020831 : Nat.Prime 2020831 := by norm_num
private theorem prime_sixtyFiveBK_2173727 : Nat.Prime 2173727 := by norm_num
private theorem prime_sixtyFiveBK_2201737 : Nat.Prime 2201737 := by norm_num
private theorem prime_sixtyFiveBK_2202149 : Nat.Prime 2202149 := by norm_num
private theorem prime_sixtyFiveBK_2241607 : Nat.Prime 2241607 := by norm_num
private theorem prime_sixtyFiveBK_2286149 : Nat.Prime 2286149 := by norm_num
private theorem prime_sixtyFiveBK_2310701 : Nat.Prime 2310701 := by norm_num
private theorem prime_sixtyFiveBK_2339039 : Nat.Prime 2339039 := by norm_num
private theorem prime_sixtyFiveBK_2386603 : Nat.Prime 2386603 := by norm_num
private theorem prime_sixtyFiveBK_2451797 : Nat.Prime 2451797 := by norm_num
private theorem prime_sixtyFiveBK_2517821 : Nat.Prime 2517821 := by norm_num
private theorem prime_sixtyFiveBK_2625653 : Nat.Prime 2625653 := by norm_num
private theorem prime_sixtyFiveBK_2766997 : Nat.Prime 2766997 := by norm_num
private theorem prime_sixtyFiveBK_2941607 : Nat.Prime 2941607 := by norm_num
private theorem prime_sixtyFiveBK_2948783 : Nat.Prime 2948783 := by norm_num
private theorem prime_sixtyFiveBK_3200401 : Nat.Prime 3200401 := by norm_num
private theorem prime_sixtyFiveBK_3298111 : Nat.Prime 3298111 := by norm_num
private theorem prime_sixtyFiveBK_3302149 : Nat.Prime 3302149 := by norm_num
private theorem prime_sixtyFiveBK_3657347 : Nat.Prime 3657347 := by norm_num
private theorem prime_sixtyFiveBK_3909467 : Nat.Prime 3909467 := by norm_num
private theorem prime_sixtyFiveBK_3969253 : Nat.Prime 3969253 := by norm_num
private theorem prime_sixtyFiveBK_4056389 : Nat.Prime 4056389 := by norm_num
private theorem prime_sixtyFiveBK_4149373 : Nat.Prime 4149373 := by norm_num
private theorem prime_sixtyFiveBK_4188853 : Nat.Prime 4188853 := by norm_num
private theorem prime_sixtyFiveBK_4340419 : Nat.Prime 4340419 := by norm_num
private theorem prime_sixtyFiveBK_4444357 : Nat.Prime 4444357 := by norm_num
private theorem prime_sixtyFiveBK_4467017 : Nat.Prime 4467017 := by norm_num
private theorem prime_sixtyFiveBK_4481101 : Nat.Prime 4481101 := by norm_num
private theorem prime_sixtyFiveBK_4610003 : Nat.Prime 4610003 := by norm_num
private theorem prime_sixtyFiveBK_4789777 : Nat.Prime 4789777 := by norm_num
private theorem prime_sixtyFiveBK_5074247 : Nat.Prime 5074247 := by norm_num
private theorem prime_sixtyFiveBK_5503033 : Nat.Prime 5503033 := by norm_num
private theorem prime_sixtyFiveBK_5619203 : Nat.Prime 5619203 := by norm_num
private theorem prime_sixtyFiveBK_5989309 : Nat.Prime 5989309 := by norm_num
private theorem prime_sixtyFiveBK_6417179 : Nat.Prime 6417179 := by norm_num
private theorem prime_sixtyFiveBK_6448807 : Nat.Prime 6448807 := by norm_num
private theorem prime_sixtyFiveBK_6478201 : Nat.Prime 6478201 := by norm_num
private theorem prime_sixtyFiveBK_6673613 : Nat.Prime 6673613 := by norm_num
private theorem prime_sixtyFiveBK_7477181 : Nat.Prime 7477181 := by norm_num
private theorem prime_sixtyFiveBK_8185157 : Nat.Prime 8185157 := by norm_num
private theorem prime_sixtyFiveBK_8342693 : Nat.Prime 8342693 := by norm_num
private theorem prime_sixtyFiveBK_8377241 : Nat.Prime 8377241 := by norm_num
private theorem prime_sixtyFiveBK_9657787 : Nat.Prime 9657787 := by norm_num
private theorem prime_sixtyFiveBK_9773209 : Nat.Prime 9773209 := by norm_num
private theorem prime_sixtyFiveBK_10058063 : Nat.Prime 10058063 := by norm_num
private theorem prime_sixtyFiveBK_10302179 : Nat.Prime 10302179 := by norm_num
private theorem prime_sixtyFiveBK_11742001 : Nat.Prime 11742001 := by norm_num
private theorem prime_sixtyFiveBK_12453923 : Nat.Prime 12453923 := by norm_num
private theorem prime_sixtyFiveBK_13036379 : Nat.Prime 13036379 := by norm_num
private theorem prime_sixtyFiveBK_13658867 : Nat.Prime 13658867 := by norm_num
private theorem prime_sixtyFiveBK_14099857 : Nat.Prime 14099857 := by norm_num
private theorem prime_sixtyFiveBK_14275507 : Nat.Prime 14275507 := by norm_num
private theorem prime_sixtyFiveBK_15520667 : Nat.Prime 15520667 := by norm_num
private theorem prime_sixtyFiveBK_17558861 : Nat.Prime 17558861 := by norm_num
private theorem prime_sixtyFiveBK_19248329 : Nat.Prime 19248329 := by norm_num
private theorem prime_sixtyFiveBK_19419989 : Nat.Prime 19419989 := by norm_num
private theorem prime_sixtyFiveBK_19944317 : Nat.Prime 19944317 := by norm_num
private theorem prime_sixtyFiveBK_20133937 : Nat.Prime 20133937 := by norm_num
private theorem prime_sixtyFiveBK_20948617 : Nat.Prime 20948617 := by norm_num
private theorem prime_sixtyFiveBK_21162871 : Nat.Prime 21162871 := by norm_num
private theorem prime_sixtyFiveBK_21458309 : Nat.Prime 21458309 := by norm_num
private theorem prime_sixtyFiveBK_22133743 : Nat.Prime 22133743 := by norm_num
private theorem prime_sixtyFiveBK_22697491 : Nat.Prime 22697491 := by norm_num
private theorem prime_sixtyFiveBK_23866291 : Nat.Prime 23866291 := by norm_num
private theorem prime_sixtyFiveBK_24624967 : Nat.Prime 24624967 := by norm_num
private theorem prime_sixtyFiveBK_24935137 : Nat.Prime 24935137 := by norm_num
private theorem prime_sixtyFiveBK_27635141 : Nat.Prime 27635141 := by norm_num
private theorem prime_sixtyFiveBK_28060997 : Nat.Prime 28060997 := by norm_num
private theorem prime_sixtyFiveBK_28334881 : Nat.Prime 28334881 := by norm_num
private theorem prime_sixtyFiveBK_29997481 : Nat.Prime 29997481 := by norm_num
private theorem prime_sixtyFiveBK_35998609 : Nat.Prime 35998609 := by
  apply lucas_primality 35998609 (14 : ZMod 35998609)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (749971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (749971, 1)] : List FactorBlock).map factorBlockValue).prod) = 35998609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_749971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 35998609) ^ 17999304 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 35998609) ^ 11999536 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 35998609) ^ 48 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_45484969 : Nat.Prime 45484969 := by
  apply lucas_primality 45484969 (11 : ZMod 45484969)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1895207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1895207, 1)] : List FactorBlock).map factorBlockValue).prod) = 45484969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_1895207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 45484969) ^ 22742484 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 45484969) ^ 15161656 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 45484969) ^ 24 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_52995497 : Nat.Prime 52995497 := by
  apply lucas_primality 52995497 (3 : ZMod 52995497)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (293, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (293, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) = 52995497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_293
      · exact prime_sixtyFiveBK_983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52995497) ^ 26497748 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 52995497) ^ 2304152 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 52995497) ^ 180872 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 52995497) ^ 53912 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_54631009 : Nat.Prime 54631009 := by
  apply lucas_primality 54631009 (7 : ZMod 54631009)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (189691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (189691, 1)] : List FactorBlock).map factorBlockValue).prod) = 54631009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_189691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 54631009) ^ 27315504 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 54631009) ^ 18210336 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 54631009) ^ 288 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_54775001 : Nat.Prime 54775001 := by
  apply lucas_primality 54775001 (11 : ZMod 54775001)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 5), (7, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 5), (7, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 54775001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 54775001) ^ 27387500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 54775001) ^ 10955000 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 54775001) ^ 7825000 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 54775001) ^ 175000 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_64372241 : Nat.Prime 64372241 := by
  apply lucas_primality 64372241 (3 : ZMod 64372241)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (804653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (804653, 1)] : List FactorBlock).map factorBlockValue).prod) = 64372241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_804653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64372241) ^ 32186120 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372241) ^ 12874448 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372241) ^ 80 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_68105467 : Nat.Prime 68105467 := by
  apply lucas_primality 68105467 (3 : ZMod 68105467)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (26459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (26459, 1)] : List FactorBlock).map factorBlockValue).prod) = 68105467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_26459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68105467) ^ 34052733 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 68105467) ^ 22701822 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 68105467) ^ 6191406 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 68105467) ^ 5238882 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 68105467) ^ 2574 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_70452007 : Nat.Prime 70452007 := by
  apply lucas_primality 70452007 (3 : ZMod 70452007)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11742001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11742001, 1)] : List FactorBlock).map factorBlockValue).prod) = 70452007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11742001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 70452007) ^ 35226003 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 70452007) ^ 23484002 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 70452007) ^ 6 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_73017733 : Nat.Prime 73017733 := by
  apply lucas_primality 73017733 (2 : ZMod 73017733)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (61, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (61, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) = 73017733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_61
      · exact prime_sixtyFiveBK_4337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73017733) ^ 36508866 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 73017733) ^ 24339244 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 73017733) ^ 3174684 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 73017733) ^ 1197012 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 73017733) ^ 16836 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_76075171 : Nat.Prime 76075171 := by
  apply lucas_primality 76075171 (10 : ZMod 76075171)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (43, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (43, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 76075171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 76075171) ^ 38037585 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76075171) ^ 25358390 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76075171) ^ 15215034 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76075171) ^ 4475010 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76075171) ^ 1769190 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76075171) ^ 21930 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_86908319 : Nat.Prime 86908319 := by
  apply lucas_primality 86908319 (11 : ZMod 86908319)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (19, 1), (19219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (19, 1), (19219, 1)] : List FactorBlock).map factorBlockValue).prod) = 86908319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_19219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 86908319) ^ 43454159 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 86908319) ^ 12415474 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 86908319) ^ 5112254 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 86908319) ^ 4574122 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 86908319) ^ 4522 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_89255791 : Nat.Prime 89255791 := by
  apply lucas_primality 89255791 (6 : ZMod 89255791)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (59, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (59, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 89255791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 89255791) ^ 44627895 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89255791) ^ 29751930 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89255791) ^ 17851158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89255791) ^ 6865830 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89255791) ^ 1512810 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89255791) ^ 207090 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_90201019 : Nat.Prime 90201019 := by
  apply lucas_primality 90201019 (10 : ZMod 90201019)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (53, 1), (14929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (53, 1), (14929, 1)] : List FactorBlock).map factorBlockValue).prod) = 90201019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_53
      · exact prime_sixtyFiveBK_14929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 90201019) ^ 45100509 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90201019) ^ 30067006 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90201019) ^ 4747422 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90201019) ^ 1701906 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90201019) ^ 6042 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_90244181 : Nat.Prime 90244181 := by
  apply lucas_primality 90244181 (3 : ZMod 90244181)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (23, 1), (15091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (23, 1), (15091, 1)] : List FactorBlock).map factorBlockValue).prod) = 90244181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_15091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 90244181) ^ 45122090 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 90244181) ^ 18048836 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 90244181) ^ 6941860 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 90244181) ^ 3923660 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 90244181) ^ 5980 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_93056021 : Nat.Prime 93056021 := by
  apply lucas_primality 93056021 (2 : ZMod 93056021)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (73, 1), (63737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (73, 1), (63737, 1)] : List FactorBlock).map factorBlockValue).prod) = 93056021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_63737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93056021) ^ 46528010 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 93056021) ^ 18611204 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 93056021) ^ 1274740 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 93056021) ^ 1460 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_106576237 : Nat.Prime 106576237 := by
  apply lucas_primality 106576237 (2 : ZMod 106576237)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (25303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (25303, 1)] : List FactorBlock).map factorBlockValue).prod) = 106576237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_25303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106576237) ^ 53288118 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106576237) ^ 35525412 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106576237) ^ 8198172 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106576237) ^ 4212 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_114400141 : Nat.Prime 114400141 := by
  apply lucas_primality 114400141 (2 : ZMod 114400141)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (19, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (19, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) = 114400141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_5903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 114400141) ^ 57200070 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 114400141) ^ 38133380 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 114400141) ^ 22880028 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 114400141) ^ 6729420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 114400141) ^ 6021060 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 114400141) ^ 19380 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_121153957 : Nat.Prime 121153957 := by
  apply lucas_primality 121153957 (2 : ZMod 121153957)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (19, 1), (67, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (19, 1), (67, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 121153957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121153957) ^ 60576978 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 40384652 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 17307708 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 11013996 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 6376524 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 1808268 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 121153957) ^ 1176252 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_123057481 : Nat.Prime 123057481 := by
  apply lucas_primality 123057481 (11 : ZMod 123057481)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (59, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (59, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 123057481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 123057481) ^ 61528740 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 41019160 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 24611496 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 17579640 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 9465960 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 2085720 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 123057481) ^ 644280 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_133102327 : Nat.Prime 133102327 := by
  apply lucas_primality 133102327 (6 : ZMod 133102327)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (401, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (401, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 133102327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_401
      · exact prime_sixtyFiveBK_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 133102327) ^ 66551163 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 133102327) ^ 44367442 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 133102327) ^ 19014618 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 133102327) ^ 331926 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 133102327) ^ 117894 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_139716949 : Nat.Prime 139716949 := by
  apply lucas_primality 139716949 (6 : ZMod 139716949)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (97841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (97841, 1)] : List FactorBlock).map factorBlockValue).prod) = 139716949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_97841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 139716949) ^ 69858474 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 139716949) ^ 46572316 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 139716949) ^ 19959564 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 139716949) ^ 8218644 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 139716949) ^ 1428 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_142977433 : Nat.Prime 142977433 := by
  apply lucas_primality 142977433 (5 : ZMod 142977433)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (89, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (89, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 142977433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_89
      · exact prime_sixtyFiveBK_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 142977433) ^ 71488716 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142977433) ^ 47659144 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142977433) ^ 10998264 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142977433) ^ 7525128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142977433) ^ 1606488 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142977433) ^ 527592 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_147439151 : Nat.Prime 147439151 := by
  apply lucas_primality 147439151 (19 : ZMod 147439151)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2948783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2948783, 1)] : List FactorBlock).map factorBlockValue).prod) = 147439151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_2948783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 147439151) ^ 73719575 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (19 : ZMod 147439151) ^ 29487830 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (19 : ZMod 147439151) ^ 50 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_151802701 : Nat.Prime 151802701 := by
  apply lucas_primality 151802701 (2 : ZMod 151802701)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (72287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (72287, 1)] : List FactorBlock).map factorBlockValue).prod) = 151802701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_72287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151802701) ^ 75901350 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 151802701) ^ 50600900 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 151802701) ^ 30360540 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 151802701) ^ 21686100 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 151802701) ^ 2100 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_159424373 : Nat.Prime 159424373 := by
  apply lucas_primality 159424373 (2 : ZMod 159424373)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (317, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (317, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 159424373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_317
      · exact prime_sixtyFiveBK_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 159424373) ^ 79712186 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 159424373) ^ 2702108 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 159424373) ^ 502916 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 159424373) ^ 74812 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_167176481 : Nat.Prime 167176481 := by
  apply lucas_primality 167176481 (3 : ZMod 167176481)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (761, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (761, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) = 167176481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_761
      · exact prime_sixtyFiveBK_1373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 167176481) ^ 83588240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 167176481) ^ 33435296 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 167176481) ^ 219680 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 167176481) ^ 121760 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_177230153 : Nat.Prime 177230153 := by
  apply lucas_primality 177230153 (3 : ZMod 177230153)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (183089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (183089, 1)] : List FactorBlock).map factorBlockValue).prod) = 177230153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_183089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 177230153) ^ 88615076 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 177230153) ^ 16111832 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 177230153) ^ 968 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_179061577 : Nat.Prime 179061577 := by
  apply lucas_primality 179061577 (13 : ZMod 179061577)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (179, 1), (41681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (179, 1), (41681, 1)] : List FactorBlock).map factorBlockValue).prod) = 179061577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_179
      · exact prime_sixtyFiveBK_41681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 179061577) ^ 89530788 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 179061577) ^ 59687192 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 179061577) ^ 1000344 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 179061577) ^ 4296 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_186667069 : Nat.Prime 186667069 := by
  apply lucas_primality 186667069 (14 : ZMod 186667069)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (523, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (523, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 186667069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_523
      · exact prime_sixtyFiveBK_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 186667069) ^ 93333534 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186667069) ^ 62222356 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186667069) ^ 26666724 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186667069) ^ 356916 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186667069) ^ 307524 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_200912911 : Nat.Prime 200912911 := by
  apply lucas_primality 200912911 (6 : ZMod 200912911)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (647, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (647, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) = 200912911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_647
      · exact prime_sixtyFiveBK_941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 200912911) ^ 100456455 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 200912911) ^ 66970970 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 200912911) ^ 40182582 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 200912911) ^ 18264810 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 200912911) ^ 310530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 200912911) ^ 213510 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_203626223 : Nat.Prime 203626223 := by
  apply lucas_primality 203626223 (5 : ZMod 203626223)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1867, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1867, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 203626223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_1867
      · exact prime_sixtyFiveBK_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 203626223) ^ 101813111 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203626223) ^ 8853314 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203626223) ^ 109066 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203626223) ^ 85882 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_225653159 : Nat.Prime 225653159 := by
  apply lucas_primality 225653159 (7 : ZMod 225653159)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (37, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (37, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) = 225653159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_8447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 225653159) ^ 112826579 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 225653159) ^ 11876482 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 225653159) ^ 6098734 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 225653159) ^ 26714 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_260651969 : Nat.Prime 260651969 := by
  apply lucas_primality 260651969 (3 : ZMod 260651969)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (31, 1), (79, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (31, 1), (79, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 260651969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_79
      · exact prime_sixtyFiveBK_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260651969) ^ 130325984 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 260651969) ^ 8408128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 260651969) ^ 3299392 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 260651969) ^ 156736 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_284406341 : Nat.Prime 284406341 := by
  apply lucas_primality 284406341 (10 : ZMod 284406341)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (127, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (127, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 284406341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_41
      · exact prime_sixtyFiveBK_127
      · exact prime_sixtyFiveBK_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 284406341) ^ 142203170 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 284406341) ^ 56881268 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 284406341) ^ 6936740 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 284406341) ^ 2239420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 284406341) ^ 104140 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_291665471 : Nat.Prime 291665471 := by
  apply lucas_primality 291665471 (11 : ZMod 291665471)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (109, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (109, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) = 291665471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_109
      · exact prime_sixtyFiveBK_9227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 291665471) ^ 145832735 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 291665471) ^ 58333094 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 291665471) ^ 10057430 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 291665471) ^ 2675830 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 291665471) ^ 31610 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_309619603 : Nat.Prime 309619603 := by
  apply lucas_primality 309619603 (3 : ZMod 309619603)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (593141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (593141, 1)] : List FactorBlock).map factorBlockValue).prod) = 309619603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_593141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 309619603) ^ 154809801 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 309619603) ^ 103206534 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 309619603) ^ 10676538 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 309619603) ^ 522 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_323801999 : Nat.Prime 323801999 := by
  apply lucas_primality 323801999 (11 : ZMod 323801999)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (12453923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (12453923, 1)] : List FactorBlock).map factorBlockValue).prod) = 323801999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_12453923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 323801999) ^ 161900999 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 323801999) ^ 24907846 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 323801999) ^ 26 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_326753783 : Nat.Prime 326753783 := by
  apply lucas_primality 326753783 (5 : ZMod 326753783)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9497, 1), (17203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9497, 1), (17203, 1)] : List FactorBlock).map factorBlockValue).prod) = 326753783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_9497
      · exact prime_sixtyFiveBK_17203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 326753783) ^ 163376891 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 326753783) ^ 34406 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 326753783) ^ 18994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_334253083 : Nat.Prime 334253083 := by
  apply lucas_primality 334253083 (3 : ZMod 334253083)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (907, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (907, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) = 334253083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_907
      · exact prime_sixtyFiveBK_3613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334253083) ^ 167126541 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 334253083) ^ 111417694 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 334253083) ^ 19661946 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 334253083) ^ 368526 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 334253083) ^ 92514 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_347984621 : Nat.Prime 347984621 := by
  apply lucas_primality 347984621 (3 : ZMod 347984621)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (947, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (947, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 347984621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_947
      · exact prime_sixtyFiveBK_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 347984621) ^ 173992310 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 347984621) ^ 69596924 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 347984621) ^ 18314980 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 347984621) ^ 367460 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 347984621) ^ 359860 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_358997707 : Nat.Prime 358997707 := by
  apply lucas_primality 358997707 (2 : ZMod 358997707)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19944317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19944317, 1)] : List FactorBlock).map factorBlockValue).prod) = 358997707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_19944317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 358997707) ^ 179498853 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 358997707) ^ 119665902 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 358997707) ^ 18 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_365785411 : Nat.Prime 365785411 := by
  apply lucas_primality 365785411 (3 : ZMod 365785411)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (433, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (433, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 365785411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_433
      · exact prime_sixtyFiveBK_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 365785411) ^ 182892705 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 365785411) ^ 121928470 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 365785411) ^ 73157082 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 365785411) ^ 12613290 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 365785411) ^ 844770 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 365785411) ^ 376710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_392819171 : Nat.Prime 392819171 := by
  apply lucas_primality 392819171 (2 : ZMod 392819171)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (2310701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (2310701, 1)] : List FactorBlock).map factorBlockValue).prod) = 392819171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_2310701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 392819171) ^ 196409585 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 392819171) ^ 78563834 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 392819171) ^ 23107010 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 392819171) ^ 170 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_418763357 : Nat.Prime 418763357 := by
  apply lucas_primality 418763357 (2 : ZMod 418763357)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (59, 1), (97, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (59, 1), (97, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 418763357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_97
      · exact prime_sixtyFiveBK_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 418763357) ^ 209381678 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 418763357) ^ 38069396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 418763357) ^ 7097684 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 418763357) ^ 4317148 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 418763357) ^ 251812 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_448832467 : Nat.Prime 448832467 := by
  apply lucas_primality 448832467 (3 : ZMod 448832467)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24935137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24935137, 1)] : List FactorBlock).map factorBlockValue).prod) = 448832467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_24935137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 448832467) ^ 224416233 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 448832467) ^ 149610822 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 448832467) ^ 18 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_471436481 : Nat.Prime 471436481 := by
  apply lucas_primality 471436481 (3 : ZMod 471436481)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (1473239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (1473239, 1)] : List FactorBlock).map factorBlockValue).prod) = 471436481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_1473239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 471436481) ^ 235718240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 471436481) ^ 94287296 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 471436481) ^ 320 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_491882411 : Nat.Prime 491882411 := by
  apply lucas_primality 491882411 (2 : ZMod 491882411)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (823, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (823, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 491882411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_823
      · exact prime_sixtyFiveBK_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 491882411) ^ 245941205 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 491882411) ^ 98376482 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 491882411) ^ 8336990 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 491882411) ^ 597670 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 491882411) ^ 485570 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_500583773 : Nat.Prime 500583773 := by
  apply lucas_primality 500583773 (2 : ZMod 500583773)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (887, 1), (10853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (887, 1), (10853, 1)] : List FactorBlock).map factorBlockValue).prod) = 500583773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_887
      · exact prime_sixtyFiveBK_10853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 500583773) ^ 250291886 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 500583773) ^ 38506444 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 500583773) ^ 564356 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 500583773) ^ 46124 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_514977929 : Nat.Prime 514977929 := by
  apply lucas_primality 514977929 (3 : ZMod 514977929)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (64372241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (64372241, 1)] : List FactorBlock).map factorBlockValue).prod) = 514977929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_64372241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 514977929) ^ 257488964 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 514977929) ^ 8 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_546889667 : Nat.Prime 546889667 := by
  apply lucas_primality 546889667 (2 : ZMod 546889667)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (337, 1), (10271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (337, 1), (10271, 1)] : List FactorBlock).map factorBlockValue).prod) = 546889667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_79
      · exact prime_sixtyFiveBK_337
      · exact prime_sixtyFiveBK_10271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 546889667) ^ 273444833 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 546889667) ^ 6922654 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 546889667) ^ 1622818 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 546889667) ^ 53246 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_568812683 : Nat.Prime 568812683 := by
  apply lucas_primality 568812683 (2 : ZMod 568812683)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (284406341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (284406341, 1)] : List FactorBlock).map factorBlockValue).prod) = 568812683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_284406341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 568812683) ^ 284406341 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 568812683) ^ 2 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_570052909 : Nat.Prime 570052909 := by
  apply lucas_primality 570052909 (6 : ZMod 570052909)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (113, 1), (8243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (113, 1), (8243, 1)] : List FactorBlock).map factorBlockValue).prod) = 570052909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_113
      · exact prime_sixtyFiveBK_8243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 570052909) ^ 285026454 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 570052909) ^ 190017636 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 570052909) ^ 33532524 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 570052909) ^ 5044716 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 570052909) ^ 69156 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_577449871 : Nat.Prime 577449871 := by
  apply lucas_primality 577449871 (3 : ZMod 577449871)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19248329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19248329, 1)] : List FactorBlock).map factorBlockValue).prod) = 577449871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_19248329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 577449871) ^ 288724935 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 577449871) ^ 192483290 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 577449871) ^ 115489974 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 577449871) ^ 30 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_587518747 : Nat.Prime 587518747 := by
  apply lucas_primality 587518747 (2 : ZMod 587518747)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (137, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (137, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod) = 587518747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_137
      · exact prime_sixtyFiveBK_9791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 587518747) ^ 293759373 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 587518747) ^ 195839582 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 587518747) ^ 8048202 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 587518747) ^ 4288458 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 587518747) ^ 60006 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_605709971 : Nat.Prime 605709971 := by
  apply lucas_primality 605709971 (6 : ZMod 605709971)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (89, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (89, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) = 605709971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_53
      · exact prime_sixtyFiveBK_89
      · exact prime_sixtyFiveBK_12841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 605709971) ^ 302854985 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 605709971) ^ 121141994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 605709971) ^ 11428490 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 605709971) ^ 6805730 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 605709971) ^ 47170 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_608520397 : Nat.Prime 608520397 := by
  apply lucas_primality 608520397 (2 : ZMod 608520397)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (4610003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (4610003, 1)] : List FactorBlock).map factorBlockValue).prod) = 608520397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_4610003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 608520397) ^ 304260198 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608520397) ^ 202840132 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608520397) ^ 55320036 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608520397) ^ 132 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_643037567 : Nat.Prime 643037567 := by
  apply lucas_primality 643037567 (5 : ZMod 643037567)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (7477181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (7477181, 1)] : List FactorBlock).map factorBlockValue).prod) = 643037567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_7477181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 643037567) ^ 321518783 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 643037567) ^ 14954362 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 643037567) ^ 86 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_653209889 : Nat.Prime 653209889 := by
  apply lucas_primality 653209889 (3 : ZMod 653209889)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1399, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1399, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) = 653209889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_1399
      · exact prime_sixtyFiveBK_14591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 653209889) ^ 326604944 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 653209889) ^ 466912 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 653209889) ^ 44768 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_872839733 : Nat.Prime 872839733 := by
  apply lucas_primality 872839733 (2 : ZMod 872839733)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (2451797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (2451797, 1)] : List FactorBlock).map factorBlockValue).prod) = 872839733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_89
      · exact prime_sixtyFiveBK_2451797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 872839733) ^ 436419866 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 872839733) ^ 9807188 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 872839733) ^ 356 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_898521263 : Nat.Prime 898521263 := by
  apply lucas_primality 898521263 (5 : ZMod 898521263)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16651, 1), (26981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16651, 1), (26981, 1)] : List FactorBlock).map factorBlockValue).prod) = 898521263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_16651
      · exact prime_sixtyFiveBK_26981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 898521263) ^ 449260631 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 898521263) ^ 53962 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 898521263) ^ 33302 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_937043059 : Nat.Prime 937043059 := by
  apply lucas_primality 937043059 (2 : ZMod 937043059)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (491, 1), (45439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (491, 1), (45439, 1)] : List FactorBlock).map factorBlockValue).prod) = 937043059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_491
      · exact prime_sixtyFiveBK_45439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 937043059) ^ 468521529 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 937043059) ^ 312347686 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 937043059) ^ 133863294 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 937043059) ^ 1908438 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 937043059) ^ 20622 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1067333599 : Nat.Prime 1067333599 := by
  apply lucas_primality 1067333599 (3 : ZMod 1067333599)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (37, 1), (178067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (37, 1), (178067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067333599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_178067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1067333599) ^ 533666799 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067333599) ^ 355777866 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067333599) ^ 28846854 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067333599) ^ 5994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1067455801 : Nat.Prime 1067455801 := by
  apply lucas_primality 1067455801 (7 : ZMod 1067455801)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (197677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (197677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067455801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_197677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1067455801) ^ 533727900 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1067455801) ^ 355818600 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1067455801) ^ 213491160 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1067455801) ^ 5400 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1137625367 : Nat.Prime 1137625367 := by
  apply lucas_primality 1137625367 (5 : ZMod 1137625367)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (568812683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (568812683, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137625367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_568812683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1137625367) ^ 568812683 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1137625367) ^ 2 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1235474941 : Nat.Prime 1235474941 := by
  apply lucas_primality 1235474941 (6 : ZMod 1235474941)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (2941607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (2941607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235474941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_2941607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1235474941) ^ 617737470 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1235474941) ^ 411824980 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1235474941) ^ 247094988 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1235474941) ^ 176496420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1235474941) ^ 420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1284527011 : Nat.Prime 1284527011 := by
  apply lucas_primality 1284527011 (2 : ZMod 1284527011)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (239, 1), (13781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (239, 1), (13781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1284527011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_239
      · exact prime_sixtyFiveBK_13781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1284527011) ^ 642263505 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284527011) ^ 428175670 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284527011) ^ 256905402 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284527011) ^ 98809770 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284527011) ^ 5374590 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1284527011) ^ 93210 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1502322037 : Nat.Prime 1502322037 := by
  apply lucas_primality 1502322037 (11 : ZMod 1502322037)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (648671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (648671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1502322037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_193
      · exact prime_sixtyFiveBK_648671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1502322037) ^ 751161018 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1502322037) ^ 500774012 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1502322037) ^ 7784052 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1502322037) ^ 2316 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1719476119 : Nat.Prime 1719476119 := by
  apply lucas_primality 1719476119 (3 : ZMod 1719476119)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5619203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5619203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1719476119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_5619203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1719476119) ^ 859738059 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1719476119) ^ 573158706 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1719476119) ^ 101145654 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1719476119) ^ 306 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1770025793 : Nat.Prime 1770025793 := by
  apply lucas_primality 1770025793 (3 : ZMod 1770025793)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (2699, 1), (10247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (2699, 1), (10247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1770025793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_2699
      · exact prime_sixtyFiveBK_10247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1770025793) ^ 885012896 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770025793) ^ 655808 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1770025793) ^ 172736 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1815423347 : Nat.Prime 1815423347 := by
  apply lucas_primality 1815423347 (2 : ZMod 1815423347)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4139, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4139, 1), (19937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1815423347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_4139
      · exact prime_sixtyFiveBK_19937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1815423347) ^ 907711673 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815423347) ^ 165038486 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815423347) ^ 438614 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815423347) ^ 91058 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2696862169 : Nat.Prime 2696862169 := by
  apply lucas_primality 2696862169 (38 : ZMod 2696862169)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (11, 1), (13, 1), (12473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (11, 1), (13, 1), (12473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2696862169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_12473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 2696862169) ^ 1348431084 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (38 : ZMod 2696862169) ^ 898954056 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (38 : ZMod 2696862169) ^ 385266024 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (38 : ZMod 2696862169) ^ 245169288 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (38 : ZMod 2696862169) ^ 207450936 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (38 : ZMod 2696862169) ^ 216216 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2907694969 : Nat.Prime 2907694969 := by
  apply lucas_primality 2907694969 (37 : ZMod 2907694969)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (121153957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (121153957, 1)] : List FactorBlock).map factorBlockValue).prod) = 2907694969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_121153957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (37 : ZMod 2907694969) ^ 1453847484 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (37 : ZMod 2907694969) ^ 969231656 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (37 : ZMod 2907694969) ^ 24 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3106033451 : Nat.Prime 3106033451 := by
  apply lucas_primality 3106033451 (6 : ZMod 3106033451)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (17, 1), (37, 1), (71, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (17, 1), (37, 1), (71, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) = 3106033451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_71
      · exact prime_sixtyFiveBK_107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3106033451) ^ 1553016725 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 621206690 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 238925650 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 182707850 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 83946850 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 43746950 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 3106033451) ^ 29028350 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3239874811 : Nat.Prime 3239874811 := by
  apply lucas_primality 3239874811 (3 : ZMod 3239874811)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (35998609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (35998609, 1)] : List FactorBlock).map factorBlockValue).prod) = 3239874811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_35998609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3239874811) ^ 1619937405 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3239874811) ^ 1079958270 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3239874811) ^ 647974962 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3239874811) ^ 90 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4302758197 : Nat.Prime 4302758197 := by
  apply lucas_primality 4302758197 (5 : ZMod 4302758197)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (379, 1), (28669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (379, 1), (28669, 1)] : List FactorBlock).map factorBlockValue).prod) = 4302758197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_379
      · exact prime_sixtyFiveBK_28669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4302758197) ^ 2151379098 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4302758197) ^ 1434252732 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4302758197) ^ 391159836 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4302758197) ^ 11352924 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4302758197) ^ 150084 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4395152387 : Nat.Prime 4395152387 := by
  apply lucas_primality 4395152387 (2 : ZMod 4395152387)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (331, 1), (288661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (331, 1), (288661, 1)] : List FactorBlock).map factorBlockValue).prod) = 4395152387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_331
      · exact prime_sixtyFiveBK_288661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4395152387) ^ 2197576193 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4395152387) ^ 191093582 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4395152387) ^ 13278406 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4395152387) ^ 15226 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4494960823 : Nat.Prime 4494960823 := by
  apply lucas_primality 4494960823 (6 : ZMod 4494960823)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (68105467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (68105467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4494960823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_68105467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4494960823) ^ 2247480411 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4494960823) ^ 1498320274 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4494960823) ^ 408632802 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4494960823) ^ 66 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4564510261 : Nat.Prime 4564510261 := by
  apply lucas_primality 4564510261 (2 : ZMod 4564510261)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (76075171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (76075171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4564510261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_76075171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4564510261) ^ 2282255130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4564510261) ^ 1521503420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4564510261) ^ 912902052 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4564510261) ^ 60 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6277129993 : Nat.Prime 6277129993 := by
  apply lucas_primality 6277129993 (15 : ZMod 6277129993)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7, 1), (229, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7, 1), (229, 1), (6043, 1)] : List FactorBlock).map factorBlockValue).prod) = 6277129993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_229
      · exact prime_sixtyFiveBK_6043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 6277129993) ^ 3138564996 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6277129993) ^ 2092376664 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6277129993) ^ 896732856 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6277129993) ^ 27411048 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 6277129993) ^ 1038744 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6342810391 : Nat.Prime 6342810391 := by
  apply lucas_primality 6342810391 (13 : ZMod 6342810391)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (1438279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (1438279, 1)] : List FactorBlock).map factorBlockValue).prod) = 6342810391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_1438279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6342810391) ^ 3171405195 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6342810391) ^ 2114270130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6342810391) ^ 1268562078 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6342810391) ^ 906115770 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 6342810391) ^ 4410 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6404734807 : Nat.Prime 6404734807 := by
  apply lucas_primality 6404734807 (5 : ZMod 6404734807)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1067455801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1067455801, 1)] : List FactorBlock).map factorBlockValue).prod) = 6404734807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_1067455801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6404734807) ^ 3202367403 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6404734807) ^ 2134911602 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6404734807) ^ 6 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6566111221 : Nat.Prime 6566111221 := by
  apply lucas_primality 6566111221 (2 : ZMod 6566111221)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 1), (1633361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 1), (1633361, 1)] : List FactorBlock).map factorBlockValue).prod) = 6566111221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_1633361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6566111221) ^ 3283055610 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566111221) ^ 2188703740 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566111221) ^ 1313222244 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566111221) ^ 98001660 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566111221) ^ 4020 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6769280611 : Nat.Prime 6769280611 := by
  apply lucas_primality 6769280611 (2 : ZMod 6769280611)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 2), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 2), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) = 6769280611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_54941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6769280611) ^ 3384640305 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6769280611) ^ 2256426870 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6769280611) ^ 1353856122 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6769280611) ^ 182953530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6769280611) ^ 123210 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6830440343 : Nat.Prime 6830440343 := by
  apply lucas_primality 6830440343 (5 : ZMod 6830440343)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (197, 1), (1576013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (197, 1), (1576013, 1)] : List FactorBlock).map factorBlockValue).prod) = 6830440343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_197
      · exact prime_sixtyFiveBK_1576013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6830440343) ^ 3415220171 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830440343) ^ 620949122 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830440343) ^ 34672286 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830440343) ^ 4334 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_7923355513 : Nat.Prime 7923355513 := by
  apply lucas_primality 7923355513 (7 : ZMod 7923355513)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19419989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19419989, 1)] : List FactorBlock).map factorBlockValue).prod) = 7923355513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_19419989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7923355513) ^ 3961677756 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7923355513) ^ 2641118504 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7923355513) ^ 466079736 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7923355513) ^ 408 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_8333206639 : Nat.Prime 8333206639 := by
  apply lucas_primality 8333206639 (15 : ZMod 8333206639)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3347, 1), (414959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3347, 1), (414959, 1)] : List FactorBlock).map factorBlockValue).prod) = 8333206639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_3347
      · exact prime_sixtyFiveBK_414959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 8333206639) ^ 4166603319 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 8333206639) ^ 2777735546 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 8333206639) ^ 2489754 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 8333206639) ^ 20082 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_11111640539 : Nat.Prime 11111640539 := by
  apply lucas_primality 11111640539 (6 : ZMod 11111640539)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (2179, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (2179, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) = 11111640539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_2179
      · exact prime_sixtyFiveBK_6521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11111640539) ^ 5555820269 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 11111640539) ^ 653625914 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 11111640539) ^ 483114806 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 11111640539) ^ 5099422 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 11111640539) ^ 1703978 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_11998798663 : Nat.Prime 11998798663 := by
  apply lucas_primality 11998798663 (3 : ZMod 11998798663)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (29, 1), (4056389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (29, 1), (4056389, 1)] : List FactorBlock).map factorBlockValue).prod) = 11998798663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_4056389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11998798663) ^ 5999399331 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998798663) ^ 3999599554 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998798663) ^ 705811686 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998798663) ^ 413751678 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11998798663) ^ 2958 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_12114199421 : Nat.Prime 12114199421 := by
  apply lucas_primality 12114199421 (2 : ZMod 12114199421)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (605709971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (605709971, 1)] : List FactorBlock).map factorBlockValue).prod) = 12114199421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_605709971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12114199421) ^ 6057099710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12114199421) ^ 2422839884 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12114199421) ^ 20 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_12189982081 : Nat.Prime 12189982081 := by
  apply lucas_primality 12189982081 (33 : ZMod 12189982081)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (571, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (571, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) = 12189982081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_571
      · exact prime_sixtyFiveBK_11119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 12189982081) ^ 6094991040 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (33 : ZMod 12189982081) ^ 4063327360 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (33 : ZMod 12189982081) ^ 2437996416 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (33 : ZMod 12189982081) ^ 21348480 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (33 : ZMod 12189982081) ^ 1096320 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_12514797937 : Nat.Prime 12514797937 := by
  apply lucas_primality 12514797937 (5 : ZMod 12514797937)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (86908319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (86908319, 1)] : List FactorBlock).map factorBlockValue).prod) = 12514797937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_86908319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12514797937) ^ 6257398968 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12514797937) ^ 4171599312 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12514797937) ^ 144 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_13421479943 : Nat.Prime 13421479943 := by
  apply lucas_primality 13421479943 (5 : ZMod 13421479943)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (359, 1), (1437913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (359, 1), (1437913, 1)] : List FactorBlock).map factorBlockValue).prod) = 13421479943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_359
      · exact prime_sixtyFiveBK_1437913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13421479943) ^ 6710739971 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 13421479943) ^ 1032421534 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 13421479943) ^ 37385738 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 13421479943) ^ 9334 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_13768443217 : Nat.Prime 13768443217 := by
  apply lucas_primality 13768443217 (20 : ZMod 13768443217)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (29, 1), (299731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (29, 1), (299731, 1)] : List FactorBlock).map factorBlockValue).prod) = 13768443217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_299731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (20 : ZMod 13768443217) ^ 6884221608 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (20 : ZMod 13768443217) ^ 4589481072 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (20 : ZMod 13768443217) ^ 1251676656 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (20 : ZMod 13768443217) ^ 474773904 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (20 : ZMod 13768443217) ^ 45936 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_15321009631 : Nat.Prime 15321009631 := by
  apply lucas_primality 15321009631 (6 : ZMod 15321009631)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1907, 1), (267803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1907, 1), (267803, 1)] : List FactorBlock).map factorBlockValue).prod) = 15321009631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_1907
      · exact prime_sixtyFiveBK_267803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15321009631) ^ 7660504815 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 15321009631) ^ 5107003210 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 15321009631) ^ 3064201926 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 15321009631) ^ 8034090 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 15321009631) ^ 57210 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_18478949033 : Nat.Prime 18478949033 := by
  apply lucas_primality 18478949033 (3 : ZMod 18478949033)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (18839, 1), (122611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (18839, 1), (122611, 1)] : List FactorBlock).map factorBlockValue).prod) = 18478949033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_18839
      · exact prime_sixtyFiveBK_122611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18478949033) ^ 9239474516 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18478949033) ^ 980888 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18478949033) ^ 150712 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_18882149927 : Nat.Prime 18882149927 := by
  apply lucas_primality 18882149927 (5 : ZMod 18882149927)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6011, 1), (1570633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6011, 1), (1570633, 1)] : List FactorBlock).map factorBlockValue).prod) = 18882149927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_6011
      · exact prime_sixtyFiveBK_1570633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18882149927) ^ 9441074963 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18882149927) ^ 3141266 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18882149927) ^ 12022 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_19194218887 : Nat.Prime 19194218887 := by
  apply lucas_primality 19194218887 (3 : ZMod 19194218887)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (557, 1), (94153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (557, 1), (94153, 1)] : List FactorBlock).map factorBlockValue).prod) = 19194218887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_61
      · exact prime_sixtyFiveBK_557
      · exact prime_sixtyFiveBK_94153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19194218887) ^ 9597109443 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19194218887) ^ 6398072962 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19194218887) ^ 314659326 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19194218887) ^ 34459998 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19194218887) ^ 203862 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_19856410073 : Nat.Prime 19856410073 := by
  apply lucas_primality 19856410073 (3 : ZMod 19856410073)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (257, 1), (9657787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (257, 1), (9657787, 1)] : List FactorBlock).map factorBlockValue).prod) = 19856410073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_257
      · exact prime_sixtyFiveBK_9657787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19856410073) ^ 9928205036 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19856410073) ^ 77262296 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19856410073) ^ 2056 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_20700486133 : Nat.Prime 20700486133 := by
  apply lucas_primality 20700486133 (2 : ZMod 20700486133)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (36671, 1), (47041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (36671, 1), (47041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20700486133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_36671
      · exact prime_sixtyFiveBK_47041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20700486133) ^ 10350243066 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20700486133) ^ 6900162044 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20700486133) ^ 564492 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20700486133) ^ 440052 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_21726314131 : Nat.Prime 21726314131 := by
  apply lucas_primality 21726314131 (12 : ZMod 21726314131)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1289, 1), (561839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1289, 1), (561839, 1)] : List FactorBlock).map factorBlockValue).prod) = 21726314131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_1289
      · exact prime_sixtyFiveBK_561839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 21726314131) ^ 10863157065 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (12 : ZMod 21726314131) ^ 7242104710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (12 : ZMod 21726314131) ^ 4345262826 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (12 : ZMod 21726314131) ^ 16855170 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (12 : ZMod 21726314131) ^ 38670 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_21759444947 : Nat.Prime 21759444947 := by
  apply lucas_primality 21759444947 (2 : ZMod 21759444947)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2741, 1), (3969253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2741, 1), (3969253, 1)] : List FactorBlock).map factorBlockValue).prod) = 21759444947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_2741
      · exact prime_sixtyFiveBK_3969253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21759444947) ^ 10879722473 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21759444947) ^ 7938506 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21759444947) ^ 5482 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25285546369 : Nat.Prime 25285546369 := by
  apply lucas_primality 25285546369 (7 : ZMod 25285546369)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (29, 2), (26099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (29, 2), (26099, 1)] : List FactorBlock).map factorBlockValue).prod) = 25285546369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_26099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25285546369) ^ 12642773184 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25285546369) ^ 8428515456 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25285546369) ^ 871915392 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25285546369) ^ 968832 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_31693422053 : Nat.Prime 31693422053 := by
  apply lucas_primality 31693422053 (2 : ZMod 31693422053)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7923355513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7923355513, 1)] : List FactorBlock).map factorBlockValue).prod) = 31693422053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7923355513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31693422053) ^ 15846711026 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31693422053) ^ 4 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_32600785717 : Nat.Prime 32600785717 := by
  apply lucas_primality 32600785717 (2 : ZMod 32600785717)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (71, 1), (472393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (71, 1), (472393, 1)] : List FactorBlock).map factorBlockValue).prod) = 32600785717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_71
      · exact prime_sixtyFiveBK_472393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32600785717) ^ 16300392858 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32600785717) ^ 10866928572 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32600785717) ^ 459165996 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 32600785717) ^ 69012 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_37624152029 : Nat.Prime 37624152029 := by
  apply lucas_primality 37624152029 (2 : ZMod 37624152029)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (159424373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (159424373, 1)] : List FactorBlock).map factorBlockValue).prod) = 37624152029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_159424373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37624152029) ^ 18812076014 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37624152029) ^ 637697492 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37624152029) ^ 236 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_39208163063 : Nat.Prime 39208163063 := by
  apply lucas_primality 39208163063 (5 : ZMod 39208163063)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (109, 1), (2020831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (109, 1), (2020831, 1)] : List FactorBlock).map factorBlockValue).prod) = 39208163063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_89
      · exact prime_sixtyFiveBK_109
      · exact prime_sixtyFiveBK_2020831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39208163063) ^ 19604081531 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39208163063) ^ 440541158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39208163063) ^ 359707918 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 39208163063) ^ 19402 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_42097379461 : Nat.Prime 42097379461 := by
  apply lucas_primality 42097379461 (2 : ZMod 42097379461)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (313, 1), (2241607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (313, 1), (2241607, 1)] : List FactorBlock).map factorBlockValue).prod) = 42097379461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_313
      · exact prime_sixtyFiveBK_2241607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42097379461) ^ 21048689730 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42097379461) ^ 14032459820 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42097379461) ^ 8419475892 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42097379461) ^ 134496420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42097379461) ^ 18780 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_52031376911 : Nat.Prime 52031376911 := by
  apply lucas_primality 52031376911 (29 : ZMod 52031376911)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (37, 1), (2287, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (37, 1), (2287, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) = 52031376911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_2287
      · exact prime_sixtyFiveBK_3617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 52031376911) ^ 26015688455 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (29 : ZMod 52031376911) ^ 10406275382 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (29 : ZMod 52031376911) ^ 3060669230 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (29 : ZMod 52031376911) ^ 1406253430 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (29 : ZMod 52031376911) ^ 22750930 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (29 : ZMod 52031376911) ^ 14385230 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_62807769337 : Nat.Prime 62807769337 := by
  apply lucas_primality 62807769337 (5 : ZMod 62807769337)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (5021, 1), (40093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (5021, 1), (40093, 1)] : List FactorBlock).map factorBlockValue).prod) = 62807769337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_5021
      · exact prime_sixtyFiveBK_40093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 62807769337) ^ 31403884668 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62807769337) ^ 20935923112 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62807769337) ^ 4831366872 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62807769337) ^ 12509016 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62807769337) ^ 1566552 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_63386844107 : Nat.Prime 63386844107 := by
  apply lucas_primality 63386844107 (2 : ZMod 63386844107)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31693422053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31693422053, 1)] : List FactorBlock).map factorBlockValue).prod) = 63386844107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_31693422053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 63386844107) ^ 31693422053 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63386844107) ^ 2 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_63942113881 : Nat.Prime 63942113881 := by
  apply lucas_primality 63942113881 (23 : ZMod 63942113881)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (37, 1), (1600153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (37, 1), (1600153, 1)] : List FactorBlock).map factorBlockValue).prod) = 63942113881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_1600153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 63942113881) ^ 31971056940 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 63942113881) ^ 21314037960 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 63942113881) ^ 12788422776 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 63942113881) ^ 1728165240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 63942113881) ^ 39960 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_65681878421 : Nat.Prime 65681878421 := by
  apply lucas_primality 65681878421 (2 : ZMod 65681878421)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (2089, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (2089, 1), (15263, 1)] : List FactorBlock).map factorBlockValue).prod) = 65681878421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_103
      · exact prime_sixtyFiveBK_2089
      · exact prime_sixtyFiveBK_15263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65681878421) ^ 32840939210 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65681878421) ^ 13136375684 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65681878421) ^ 637688140 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65681878421) ^ 31441780 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 65681878421) ^ 4303340 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_88192594141 : Nat.Prime 88192594141 := by
  apply lucas_primality 88192594141 (2 : ZMod 88192594141)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (29997481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (29997481, 1)] : List FactorBlock).map factorBlockValue).prod) = 88192594141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_29997481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88192594141) ^ 44096297070 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88192594141) ^ 29397531380 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88192594141) ^ 17638518828 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88192594141) ^ 12598942020 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88192594141) ^ 2940 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_88216382251 : Nat.Prime 88216382251 := by
  apply lucas_primality 88216382251 (2 : ZMod 88216382251)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (31, 1), (331, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (31, 1), (331, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 88216382251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_331
      · exact prime_sixtyFiveBK_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88216382251) ^ 44108191125 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88216382251) ^ 29405460750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88216382251) ^ 17643276450 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88216382251) ^ 2845689750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88216382251) ^ 266514750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88216382251) ^ 23087250 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_92766319649 : Nat.Prime 92766319649 := by
  apply lucas_primality 92766319649 (3 : ZMod 92766319649)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (167, 1), (2239, 1), (7753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (167, 1), (2239, 1), (7753, 1)] : List FactorBlock).map factorBlockValue).prod) = 92766319649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_167
      · exact prime_sixtyFiveBK_2239
      · exact prime_sixtyFiveBK_7753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 92766319649) ^ 46383159824 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 92766319649) ^ 555486944 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 92766319649) ^ 41432032 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 92766319649) ^ 11965216 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_118313038169 : Nat.Prime 118313038169 := by
  apply lucas_primality 118313038169 (3 : ZMod 118313038169)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (1137625367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (1137625367, 1)] : List FactorBlock).map factorBlockValue).prod) = 118313038169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_1137625367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 118313038169) ^ 59156519084 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 118313038169) ^ 9101002936 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 118313038169) ^ 104 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_119138460439 : Nat.Prime 119138460439 := by
  apply lucas_primality 119138460439 (3 : ZMod 119138460439)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19856410073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19856410073, 1)] : List FactorBlock).map factorBlockValue).prod) = 119138460439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_19856410073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 119138460439) ^ 59569230219 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119138460439) ^ 39712820146 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119138460439) ^ 6 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_139218845869 : Nat.Prime 139218845869 := by
  apply lucas_primality 139218845869 (2 : ZMod 139218845869)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (863, 1), (4481101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (863, 1), (4481101, 1)] : List FactorBlock).map factorBlockValue).prod) = 139218845869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_863
      · exact prime_sixtyFiveBK_4481101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139218845869) ^ 69609422934 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139218845869) ^ 46406281956 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139218845869) ^ 161319636 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139218845869) ^ 31068 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_167437146197 : Nat.Prime 167437146197 := by
  apply lucas_primality 167437146197 (2 : ZMod 167437146197)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (120431, 1), (347579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (120431, 1), (347579, 1)] : List FactorBlock).map factorBlockValue).prod) = 167437146197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_120431
      · exact prime_sixtyFiveBK_347579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167437146197) ^ 83718573098 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 167437146197) ^ 1390316 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 167437146197) ^ 481724 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_208550811137 : Nat.Prime 208550811137 := by
  apply lucas_primality 208550811137 (3 : ZMod 208550811137)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (757, 1), (538079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (757, 1), (538079, 1)] : List FactorBlock).map factorBlockValue).prod) = 208550811137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_757
      · exact prime_sixtyFiveBK_538079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208550811137) ^ 104275405568 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 208550811137) ^ 275496448 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 208550811137) ^ 387584 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_212428782581 : Nat.Prime 212428782581 := by
  apply lucas_primality 212428782581 (2 : ZMod 212428782581)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (17, 1), (89255791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (17, 1), (89255791, 1)] : List FactorBlock).map factorBlockValue).prod) = 212428782581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_89255791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212428782581) ^ 106214391290 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212428782581) ^ 42485756516 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212428782581) ^ 30346968940 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212428782581) ^ 12495810740 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212428782581) ^ 2380 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_228341174077 : Nat.Prime 228341174077 := by
  apply lucas_primality 228341174077 (5 : ZMod 228341174077)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6342810391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6342810391, 1)] : List FactorBlock).map factorBlockValue).prod) = 228341174077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_6342810391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 228341174077) ^ 114170587038 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 228341174077) ^ 76113724692 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 228341174077) ^ 36 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_318300284693 : Nat.Prime 318300284693 := by
  apply lucas_primality 318300284693 (2 : ZMod 318300284693)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (5743, 1), (1065847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (5743, 1), (1065847, 1)] : List FactorBlock).map factorBlockValue).prod) = 318300284693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_5743
      · exact prime_sixtyFiveBK_1065847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 318300284693) ^ 159150142346 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 318300284693) ^ 24484637284 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 318300284693) ^ 55424044 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 318300284693) ^ 298636 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_434529817583 : Nat.Prime 434529817583 := by
  apply lucas_primality 434529817583 (7 : ZMod 434529817583)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11821, 1), (2625653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11821, 1), (2625653, 1)] : List FactorBlock).map factorBlockValue).prod) = 434529817583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_11821
      · exact prime_sixtyFiveBK_2625653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 434529817583) ^ 217264908791 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 434529817583) ^ 62075688226 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 434529817583) ^ 36759142 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 434529817583) ^ 165494 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_447015399829 : Nat.Prime 447015399829 := by
  apply lucas_primality 447015399829 (2 : ZMod 447015399829)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (1284527011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (1284527011, 1)] : List FactorBlock).map factorBlockValue).prod) = 447015399829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_1284527011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 447015399829) ^ 223507699914 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 447015399829) ^ 149005133276 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 447015399829) ^ 15414324132 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 447015399829) ^ 348 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_468056575997 : Nat.Prime 468056575997 := by
  apply lucas_primality 468056575997 (2 : ZMod 468056575997)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (523, 1), (1123, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (523, 1), (1123, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 468056575997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_167
      · exact prime_sixtyFiveBK_523
      · exact prime_sixtyFiveBK_1123
      · exact prime_sixtyFiveBK_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 468056575997) ^ 234028287998 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 468056575997) ^ 2802733988 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 468056575997) ^ 894945652 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 468056575997) ^ 416791252 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 468056575997) ^ 392335772 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_636600569387 : Nat.Prime 636600569387 := by
  apply lucas_primality 636600569387 (2 : ZMod 636600569387)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (318300284693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (318300284693, 1)] : List FactorBlock).map factorBlockValue).prod) = 636600569387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_318300284693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 636600569387) ^ 318300284693 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 636600569387) ^ 2 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_683613618011 : Nat.Prime 683613618011 := by
  apply lucas_primality 683613618011 (6 : ZMod 683613618011)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (4241, 1), (435653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (4241, 1), (435653, 1)] : List FactorBlock).map factorBlockValue).prod) = 683613618011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_4241
      · exact prime_sixtyFiveBK_435653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 683613618011) ^ 341806809005 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 683613618011) ^ 136722723602 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 683613618011) ^ 18476043730 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 683613618011) ^ 161191610 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 683613618011) ^ 1569170 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_693900573203 : Nat.Prime 693900573203 := by
  apply lucas_primality 693900573203 (2 : ZMod 693900573203)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (107, 1), (337, 1), (260047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (107, 1), (337, 1), (260047, 1)] : List FactorBlock).map factorBlockValue).prod) = 693900573203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_107
      · exact prime_sixtyFiveBK_337
      · exact prime_sixtyFiveBK_260047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 693900573203) ^ 346950286601 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693900573203) ^ 18754069546 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693900573203) ^ 6485052086 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693900573203) ^ 2059052146 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693900573203) ^ 2668366 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1023349183697 : Nat.Prime 1023349183697 := by
  apply lucas_primality 1023349183697 (3 : ZMod 1023349183697)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2767, 1), (3302149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2767, 1), (3302149, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023349183697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_2767
      · exact prime_sixtyFiveBK_3302149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1023349183697) ^ 511674591848 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1023349183697) ^ 146192740528 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1023349183697) ^ 369840688 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1023349183697) ^ 309904 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1026744061571 : Nat.Prime 1026744061571 := by
  apply lucas_primality 1026744061571 (2 : ZMod 1026744061571)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (127, 1), (1109, 1), (8191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (127, 1), (1109, 1), (8191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026744061571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_89
      · exact prime_sixtyFiveBK_127
      · exact prime_sixtyFiveBK_1109
      · exact prime_sixtyFiveBK_8191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1026744061571) ^ 513372030785 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026744061571) ^ 205348812314 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026744061571) ^ 11536450130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026744061571) ^ 8084598910 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026744061571) ^ 925828730 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026744061571) ^ 125350270 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1315062360739 : Nat.Prime 1315062360739 := by
  apply lucas_primality 1315062360739 (3 : ZMod 1315062360739)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (1931, 1), (772139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (1931, 1), (772139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1315062360739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_1931
      · exact prime_sixtyFiveBK_772139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1315062360739) ^ 657531180369 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315062360739) ^ 438354120246 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315062360739) ^ 187866051534 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315062360739) ^ 681026598 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315062360739) ^ 1703142 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1326494527573 : Nat.Prime 1326494527573 := by
  apply lucas_primality 1326494527573 (5 : ZMod 1326494527573)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8093, 1), (13658867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8093, 1), (13658867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1326494527573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_8093
      · exact prime_sixtyFiveBK_13658867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1326494527573) ^ 663247263786 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1326494527573) ^ 442164842524 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1326494527573) ^ 163906404 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1326494527573) ^ 97116 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1454193733763 : Nat.Prime 1454193733763 := by
  apply lucas_primality 1454193733763 (2 : ZMod 1454193733763)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (67, 1), (20133937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (67, 1), (20133937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454193733763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_20133937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1454193733763) ^ 727096866881 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454193733763) ^ 207741961966 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454193733763) ^ 132199430342 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454193733763) ^ 21704384086 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454193733763) ^ 72226 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1530018636833 : Nat.Prime 1530018636833 := by
  apply lucas_primality 1530018636833 (3 : ZMod 1530018636833)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (6830440343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (6830440343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530018636833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_6830440343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1530018636833) ^ 765009318416 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1530018636833) ^ 218574090976 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1530018636833) ^ 224 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1685400453419 : Nat.Prime 1685400453419 := by
  apply lucas_primality 1685400453419 (2 : ZMod 1685400453419)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (26813, 1), (150377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (26813, 1), (150377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1685400453419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_26813
      · exact prime_sixtyFiveBK_150377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1685400453419) ^ 842700226709 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685400453419) ^ 153218223038 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685400453419) ^ 88705287022 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685400453419) ^ 62857586 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685400453419) ^ 11207834 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1855059384637 : Nat.Prime 1855059384637 := by
  apply lucas_primality 1855059384637 (6 : ZMod 1855059384637)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (571, 1), (90244181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (571, 1), (90244181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1855059384637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_571
      · exact prime_sixtyFiveBK_90244181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1855059384637) ^ 927529692318 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1855059384637) ^ 618353128212 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1855059384637) ^ 3248790516 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1855059384637) ^ 20556 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2820216080329 : Nat.Prime 2820216080329 := by
  apply lucas_primality 2820216080329 (11 : ZMod 2820216080329)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (797, 1), (147439151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (797, 1), (147439151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820216080329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_797
      · exact prime_sixtyFiveBK_147439151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2820216080329) ^ 1410108040164 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2820216080329) ^ 940072026776 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2820216080329) ^ 3538539624 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2820216080329) ^ 19128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3262130185667 : Nat.Prime 3262130185667 := by
  apply lucas_primality 3262130185667 (2 : ZMod 3262130185667)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (227, 1), (653209889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (227, 1), (653209889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3262130185667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_227
      · exact prime_sixtyFiveBK_653209889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3262130185667) ^ 1631065092833 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3262130185667) ^ 296557289606 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3262130185667) ^ 14370617558 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3262130185667) ^ 4994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3370800906839 : Nat.Prime 3370800906839 := by
  apply lucas_primality 3370800906839 (7 : ZMod 3370800906839)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1685400453419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1685400453419, 1)] : List FactorBlock).map factorBlockValue).prod) = 3370800906839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_1685400453419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 3370800906839) ^ 1685400453419 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3370800906839) ^ 2 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3461639254277 : Nat.Prime 3461639254277 := by
  apply lucas_primality 3461639254277 (2 : ZMod 3461639254277)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (73, 1), (54631009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (73, 1), (54631009, 1)] : List FactorBlock).map factorBlockValue).prod) = 3461639254277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_54631009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3461639254277) ^ 1730819627138 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3461639254277) ^ 494519893468 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3461639254277) ^ 111665782396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3461639254277) ^ 47419715812 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3461639254277) ^ 63364 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3466568502671 : Nat.Prime 3466568502671 := by
  apply lucas_primality 3466568502671 (7 : ZMod 3466568502671)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (17957, 1), (212141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (17957, 1), (212141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3466568502671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_17957
      · exact prime_sixtyFiveBK_212141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3466568502671) ^ 1733284251335 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3466568502671) ^ 693313700534 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3466568502671) ^ 495224071810 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3466568502671) ^ 266659115590 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3466568502671) ^ 193048310 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3466568502671) ^ 16340870 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3747558555773 : Nat.Prime 3747558555773 := by
  apply lucas_primality 3747558555773 (2 : ZMod 3747558555773)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (8233, 1), (5989309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (8233, 1), (5989309, 1)] : List FactorBlock).map factorBlockValue).prod) = 3747558555773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_8233
      · exact prime_sixtyFiveBK_5989309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3747558555773) ^ 1873779277886 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3747558555773) ^ 197239923988 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3747558555773) ^ 455187484 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3747558555773) ^ 625708 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3819603416323 : Nat.Prime 3819603416323 := by
  apply lucas_primality 3819603416323 (7 : ZMod 3819603416323)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (636600569387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (636600569387, 1)] : List FactorBlock).map factorBlockValue).prod) = 3819603416323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_636600569387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3819603416323) ^ 1909801708161 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3819603416323) ^ 1273201138774 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3819603416323) ^ 6 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3950182282583 : Nat.Prime 3950182282583 := by
  apply lucas_primality 3950182282583 (5 : ZMod 3950182282583)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (31, 1), (107, 1), (389, 1), (52783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (31, 1), (107, 1), (389, 1), (52783, 1)] : List FactorBlock).map factorBlockValue).prod) = 3950182282583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_107
      · exact prime_sixtyFiveBK_389
      · exact prime_sixtyFiveBK_52783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3950182282583) ^ 1975091141291 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950182282583) ^ 136213182158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950182282583) ^ 127425234922 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950182282583) ^ 36917591426 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950182282583) ^ 10154710238 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3950182282583) ^ 74838154 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4097058239699 : Nat.Prime 4097058239699 := by
  apply lucas_primality 4097058239699 (2 : ZMod 4097058239699)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1109, 1), (11831, 1), (156131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1109, 1), (11831, 1), (156131, 1)] : List FactorBlock).map factorBlockValue).prod) = 4097058239699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_1109
      · exact prime_sixtyFiveBK_11831
      · exact prime_sixtyFiveBK_156131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4097058239699) ^ 2048529119849 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097058239699) ^ 3694371722 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097058239699) ^ 346298558 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097058239699) ^ 26241158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4272852434363 : Nat.Prime 4272852434363 := by
  apply lucas_primality 4272852434363 (2 : ZMod 4272852434363)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (108271, 1), (533303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (108271, 1), (533303, 1)] : List FactorBlock).map factorBlockValue).prod) = 4272852434363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_108271
      · exact prime_sixtyFiveBK_533303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4272852434363) ^ 2136426217181 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4272852434363) ^ 115482498226 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4272852434363) ^ 39464422 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4272852434363) ^ 8012054 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4866565441501 : Nat.Prime 4866565441501 := by
  apply lucas_primality 4866565441501 (6 : ZMod 4866565441501)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 3), (7, 1), (43, 1), (239, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 3), (7, 1), (43, 1), (239, 1), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4866565441501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_239
      · exact prime_sixtyFiveBK_5011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4866565441501) ^ 2433282720750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 1622188480500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 973313088300 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 695223634500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 113175940500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 20362198500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4866565441501) ^ 971176500 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4871772705773 : Nat.Prime 4871772705773 := by
  apply lucas_primality 4871772705773 (2 : ZMod 4871772705773)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (733, 1), (8185157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (733, 1), (8185157, 1)] : List FactorBlock).map factorBlockValue).prod) = 4871772705773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_733
      · exact prime_sixtyFiveBK_8185157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4871772705773) ^ 2435886352886 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4871772705773) ^ 695967529396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4871772705773) ^ 167992162268 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4871772705773) ^ 6646347484 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4871772705773) ^ 595196 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_5432178877733 : Nat.Prime 5432178877733 := by
  apply lucas_primality 5432178877733 (2 : ZMod 5432178877733)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (409, 1), (45484969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (409, 1), (45484969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5432178877733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_409
      · exact prime_sixtyFiveBK_45484969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5432178877733) ^ 2716089438866 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5432178877733) ^ 74413409284 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5432178877733) ^ 13281610948 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5432178877733) ^ 119428 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_5934982019839 : Nat.Prime 5934982019839 := by
  apply lucas_primality 5934982019839 (3 : ZMod 5934982019839)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1487, 1), (21458309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1487, 1), (21458309, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934982019839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_1487
      · exact prime_sixtyFiveBK_21458309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934982019839) ^ 2967491009919 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934982019839) ^ 1978327339946 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934982019839) ^ 191451032898 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934982019839) ^ 3991245474 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934982019839) ^ 276582 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_5989878258391 : Nat.Prime 5989878258391 := by
  apply lucas_primality 5989878258391 (11 : ZMod 5989878258391)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (509, 1), (10058063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (509, 1), (10058063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5989878258391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_509
      · exact prime_sixtyFiveBK_10058063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5989878258391) ^ 2994939129195 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5989878258391) ^ 1996626086130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5989878258391) ^ 1197975651678 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5989878258391) ^ 460759866030 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5989878258391) ^ 11767933710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5989878258391) ^ 595530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6095341103147 : Nat.Prime 6095341103147 := by
  apply lucas_primality 6095341103147 (2 : ZMod 6095341103147)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (3659, 1), (2386603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (3659, 1), (2386603, 1)] : List FactorBlock).map factorBlockValue).prod) = 6095341103147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_349
      · exact prime_sixtyFiveBK_3659
      · exact prime_sixtyFiveBK_2386603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6095341103147) ^ 3047670551573 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6095341103147) ^ 17465160754 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6095341103147) ^ 1665848894 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6095341103147) ^ 2553982 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6425981107813 : Nat.Prime 6425981107813 := by
  apply lucas_primality 6425981107813 (5 : ZMod 6425981107813)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (37, 1), (41, 1), (461, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (37, 1), (41, 1), (461, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) = 6425981107813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_41
      · exact prime_sixtyFiveBK_461
      · exact prime_sixtyFiveBK_5209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6425981107813) ^ 3212990553906 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 2141993702604 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 917997301116 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 173675165076 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 156731246532 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 13939221492 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6425981107813) ^ 1233630468 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6856817521973 : Nat.Prime 6856817521973 := by
  apply lucas_primality 6856817521973 (2 : ZMod 6856817521973)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (43, 1), (173, 1), (20948617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (43, 1), (173, 1), (20948617, 1)] : List FactorBlock).map factorBlockValue).prod) = 6856817521973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_173
      · exact prime_sixtyFiveBK_20948617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6856817521973) ^ 3428408760986 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856817521973) ^ 623347047452 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856817521973) ^ 159460872604 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856817521973) ^ 39634783364 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856817521973) ^ 327316 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_8982894439117 : Nat.Prime 8982894439117 := by
  apply lucas_primality 8982894439117 (2 : ZMod 8982894439117)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (19194218887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (19194218887, 1)] : List FactorBlock).map factorBlockValue).prod) = 8982894439117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_19194218887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8982894439117) ^ 4491447219558 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8982894439117) ^ 2994298146372 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8982894439117) ^ 690991879932 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8982894439117) ^ 468 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_11280864321317 : Nat.Prime 11280864321317 := by
  apply lucas_primality 11280864321317 (2 : ZMod 11280864321317)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2820216080329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2820216080329, 1)] : List FactorBlock).map factorBlockValue).prod) = 11280864321317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_2820216080329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11280864321317) ^ 5640432160658 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11280864321317) ^ 4 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_13715116766557 : Nat.Prime 13715116766557 := by
  apply lucas_primality 13715116766557 (2 : ZMod 13715116766557)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (211, 1), (349, 1), (15520667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (211, 1), (349, 1), (15520667, 1)] : List FactorBlock).map factorBlockValue).prod) = 13715116766557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_211
      · exact prime_sixtyFiveBK_349
      · exact prime_sixtyFiveBK_15520667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13715116766557) ^ 6857558383278 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13715116766557) ^ 4571705588852 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13715116766557) ^ 65000553396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13715116766557) ^ 39298328844 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13715116766557) ^ 883668 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_18895744228343 : Nat.Prime 18895744228343 := by
  apply lucas_primality 18895744228343 (5 : ZMod 18895744228343)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (281, 1), (225653159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (281, 1), (225653159, 1)] : List FactorBlock).map factorBlockValue).prod) = 18895744228343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_149
      · exact prime_sixtyFiveBK_281
      · exact prime_sixtyFiveBK_225653159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18895744228343) ^ 9447872114171 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18895744228343) ^ 126817075358 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18895744228343) ^ 67244641382 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18895744228343) ^ 83738 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_20431710189623 : Nat.Prime 20431710189623 := by
  apply lucas_primality 20431710189623 (5 : ZMod 20431710189623)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (593, 1), (7823, 1), (2202149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (593, 1), (7823, 1), (2202149, 1)] : List FactorBlock).map factorBlockValue).prod) = 20431710189623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_593
      · exact prime_sixtyFiveBK_7823
      · exact prime_sixtyFiveBK_2202149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20431710189623) ^ 10215855094811 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20431710189623) ^ 34454823254 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20431710189623) ^ 2611748714 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20431710189623) ^ 9278078 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_23859905755271 : Nat.Prime 23859905755271 := by
  apply lucas_primality 23859905755271 (11 : ZMod 23859905755271)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (37, 1), (773, 1), (6417179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (37, 1), (773, 1), (6417179, 1)] : List FactorBlock).map factorBlockValue).prod) = 23859905755271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_773
      · exact prime_sixtyFiveBK_6417179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23859905755271) ^ 11929952877635 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 23859905755271) ^ 4771981151054 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 23859905755271) ^ 1835377365790 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 23859905755271) ^ 644862317710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 23859905755271) ^ 30866630990 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 23859905755271) ^ 3718130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25133115589811 : Nat.Prime 25133115589811 := by
  apply lucas_primality 25133115589811 (2 : ZMod 25133115589811)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6871, 1), (365785411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6871, 1), (365785411, 1)] : List FactorBlock).map factorBlockValue).prod) = 25133115589811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_6871
      · exact prime_sixtyFiveBK_365785411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25133115589811) ^ 12566557794905 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25133115589811) ^ 5026623117962 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25133115589811) ^ 3657854110 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25133115589811) ^ 68710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25665601985087 : Nat.Prime 25665601985087 := by
  apply lucas_primality 25665601985087 (5 : ZMod 25665601985087)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (61, 1), (186667069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (61, 1), (186667069, 1)] : List FactorBlock).map factorBlockValue).prod) = 25665601985087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_61
      · exact prime_sixtyFiveBK_186667069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25665601985087) ^ 12832800992543 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25665601985087) ^ 3666514569298 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25665601985087) ^ 1115895738482 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25665601985087) ^ 420747573526 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25665601985087) ^ 137494 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_30614779342489 : Nat.Prime 30614779342489 := by
  apply lucas_primality 30614779342489 (7 : ZMod 30614779342489)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (43, 1), (2696862169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (43, 1), (2696862169, 1)] : List FactorBlock).map factorBlockValue).prod) = 30614779342489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_2696862169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30614779342489) ^ 15307389671244 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 30614779342489) ^ 10204926447496 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 30614779342489) ^ 2783161758408 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 30614779342489) ^ 711971612616 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 30614779342489) ^ 11352 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_42384044316683 : Nat.Prime 42384044316683 := by
  apply lucas_primality 42384044316683 (2 : ZMod 42384044316683)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (683613618011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (683613618011, 1)] : List FactorBlock).map factorBlockValue).prod) = 42384044316683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_683613618011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42384044316683) ^ 21192022158341 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42384044316683) ^ 1367227236022 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 42384044316683) ^ 62 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_55706074098923 : Nat.Prime 55706074098923 := by
  apply lucas_primality 55706074098923 (2 : ZMod 55706074098923)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (131, 1), (347984621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (131, 1), (347984621, 1)] : List FactorBlock).map factorBlockValue).prod) = 55706074098923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_131
      · exact prime_sixtyFiveBK_347984621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55706074098923) ^ 27853037049461 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55706074098923) ^ 4285082622994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55706074098923) ^ 1185235619126 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55706074098923) ^ 425237206862 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55706074098923) ^ 160082 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_67668945978313 : Nat.Prime 67668945978313 := by
  apply lucas_primality 67668945978313 (10 : ZMod 67668945978313)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7, 1), (41, 1), (59, 2), (104527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7, 1), (41, 1), (59, 2), (104527, 1)] : List FactorBlock).map factorBlockValue).prod) = 67668945978313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_41
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_104527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 67668945978313) ^ 33834472989156 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 67668945978313) ^ 22556315326104 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 67668945978313) ^ 9666992282616 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 67668945978313) ^ 1650462097032 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 67668945978313) ^ 1146931287768 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 67668945978313) ^ 647382456 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_68443036627897 : Nat.Prime 68443036627897 := by
  apply lucas_primality 68443036627897 (5 : ZMod 68443036627897)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (521, 1), (260651969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (521, 1), (260651969, 1)] : List FactorBlock).map factorBlockValue).prod) = 68443036627897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_521
      · exact prime_sixtyFiveBK_260651969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68443036627897) ^ 34221518313948 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 68443036627897) ^ 22814345542632 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 68443036627897) ^ 9777576661128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 68443036627897) ^ 131368592376 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 68443036627897) ^ 262584 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_88763884235591 : Nat.Prime 88763884235591 := by
  apply lucas_primality 88763884235591 (13 : ZMod 88763884235591)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (193, 1), (15017, 1), (27103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (193, 1), (15017, 1), (27103, 1)] : List FactorBlock).map factorBlockValue).prod) = 88763884235591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_113
      · exact prime_sixtyFiveBK_193
      · exact prime_sixtyFiveBK_15017
      · exact prime_sixtyFiveBK_27103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 88763884235591) ^ 44381942117795 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 88763884235591) ^ 17752776847118 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 88763884235591) ^ 785521099430 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 88763884235591) ^ 459916498630 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 88763884235591) ^ 5910893270 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 88763884235591) ^ 3275057530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_89775625903813 : Nat.Prime 89775625903813 := by
  apply lucas_primality 89775625903813 (5 : ZMod 89775625903813)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (127, 1), (117841, 1), (166631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (127, 1), (117841, 1), (166631, 1)] : List FactorBlock).map factorBlockValue).prod) = 89775625903813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_127
      · exact prime_sixtyFiveBK_117841
      · exact prime_sixtyFiveBK_166631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 89775625903813) ^ 44887812951906 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 89775625903813) ^ 29925208634604 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 89775625903813) ^ 706894692156 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 89775625903813) ^ 761836932 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 89775625903813) ^ 538769052 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_91544537695823 : Nat.Prime 91544537695823 := by
  apply lucas_primality 91544537695823 (5 : ZMod 91544537695823)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1327, 1), (1815423347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1327, 1), (1815423347, 1)] : List FactorBlock).map factorBlockValue).prod) = 91544537695823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_1327
      · exact prime_sixtyFiveBK_1815423347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91544537695823) ^ 45772268847911 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 91544537695823) ^ 4818133562938 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 91544537695823) ^ 68986087186 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 91544537695823) ^ 50426 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_135154578931291 : Nat.Prime 135154578931291 := by
  apply lucas_primality 135154578931291 (2 : ZMod 135154578931291)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (46691, 1), (606847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (46691, 1), (606847, 1)] : List FactorBlock).map factorBlockValue).prod) = 135154578931291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_53
      · exact prime_sixtyFiveBK_46691
      · exact prime_sixtyFiveBK_606847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135154578931291) ^ 67577289465645 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135154578931291) ^ 45051526310430 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135154578931291) ^ 27030915786258 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135154578931291) ^ 2550086394930 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135154578931291) ^ 2894660190 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135154578931291) ^ 222716070 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_137668587273043 : Nat.Prime 137668587273043 := by
  apply lucas_primality 137668587273043 (2 : ZMod 137668587273043)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (67, 1), (109, 1), (448832467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (67, 1), (109, 1), (448832467, 1)] : List FactorBlock).map factorBlockValue).prod) = 137668587273043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_109
      · exact prime_sixtyFiveBK_448832467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137668587273043) ^ 68834293636521 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137668587273043) ^ 45889529091014 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137668587273043) ^ 19666941039006 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137668587273043) ^ 2054755033926 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137668587273043) ^ 1263014562138 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137668587273043) ^ 306726 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_140687033232589 : Nat.Prime 140687033232589 := by
  apply lucas_primality 140687033232589 (6 : ZMod 140687033232589)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (3691, 1), (167176481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (3691, 1), (167176481, 1)] : List FactorBlock).map factorBlockValue).prod) = 140687033232589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_3691
      · exact prime_sixtyFiveBK_167176481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140687033232589) ^ 70343516616294 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140687033232589) ^ 46895677744196 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140687033232589) ^ 7404580696452 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140687033232589) ^ 38116237668 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140687033232589) ^ 841548 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_140935668093223 : Nat.Prime 140935668093223 := by
  apply lucas_primality 140935668093223 (6 : ZMod 140935668093223)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (409, 1), (1553, 1), (786823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (409, 1), (1553, 1), (786823, 1)] : List FactorBlock).map factorBlockValue).prod) = 140935668093223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_409
      · exact prime_sixtyFiveBK_1553
      · exact prime_sixtyFiveBK_786823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140935668093223) ^ 70467834046611 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140935668093223) ^ 46978556031074 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140935668093223) ^ 2998631236026 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140935668093223) ^ 344585985558 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140935668093223) ^ 90750591174 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 140935668093223) ^ 179119914 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_208574312439841 : Nat.Prime 208574312439841 := by
  apply lucas_primality 208574312439841 (7 : ZMod 208574312439841)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (434529817583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (434529817583, 1)] : List FactorBlock).map factorBlockValue).prod) = 208574312439841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_434529817583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 208574312439841) ^ 104287156219920 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 208574312439841) ^ 69524770813280 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 208574312439841) ^ 41714862487968 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 208574312439841) ^ 480 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_249269244833239 : Nat.Prime 249269244833239 := by
  apply lucas_primality 249269244833239 (7 : ZMod 249269244833239)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5934982019839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5934982019839, 1)] : List FactorBlock).map factorBlockValue).prod) = 249269244833239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_5934982019839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 249269244833239) ^ 124634622416619 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 249269244833239) ^ 83089748277746 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 249269244833239) ^ 35609892119034 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 249269244833239) ^ 42 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_307645375274137 : Nat.Prime 307645375274137 := by
  apply lucas_primality 307645375274137 (5 : ZMod 307645375274137)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4272852434363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4272852434363, 1)] : List FactorBlock).map factorBlockValue).prod) = 307645375274137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_4272852434363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 307645375274137) ^ 153822687637068 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 307645375274137) ^ 102548458424712 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 307645375274137) ^ 72 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_359102503615253 : Nat.Prime 359102503615253 := by
  apply lucas_primality 359102503615253 (2 : ZMod 359102503615253)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89775625903813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89775625903813, 1)] : List FactorBlock).map factorBlockValue).prod) = 359102503615253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_89775625903813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 359102503615253) ^ 179551251807626 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 359102503615253) ^ 4 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_418442578941319 : Nat.Prime 418442578941319 := by
  apply lucas_primality 418442578941319 (6 : ZMod 418442578941319)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (468056575997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (468056575997, 1)] : List FactorBlock).map factorBlockValue).prod) = 418442578941319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_149
      · exact prime_sixtyFiveBK_468056575997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 418442578941319) ^ 209221289470659 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 418442578941319) ^ 139480859647106 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 418442578941319) ^ 2808339455982 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 418442578941319) ^ 894 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_581555394718537 : Nat.Prime 581555394718537 := by
  apply lucas_primality 581555394718537 (5 : ZMod 581555394718537)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (3461639254277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (3461639254277, 1)] : List FactorBlock).map factorBlockValue).prod) = 581555394718537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_3461639254277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 581555394718537) ^ 290777697359268 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 581555394718537) ^ 193851798239512 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 581555394718537) ^ 83079342102648 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 581555394718537) ^ 168 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_795232380188989 : Nat.Prime 795232380188989 := by
  apply lucas_primality 795232380188989 (6 : ZMod 795232380188989)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (263, 1), (11998798663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (263, 1), (11998798663, 1)] : List FactorBlock).map factorBlockValue).prod) = 795232380188989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_263
      · exact prime_sixtyFiveBK_11998798663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 795232380188989) ^ 397616190094494 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 795232380188989) ^ 265077460062996 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 795232380188989) ^ 113604625741284 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 795232380188989) ^ 3023697263076 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 795232380188989) ^ 66276 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_927191293920799 : Nat.Prime 927191293920799 := by
  apply lucas_primality 927191293920799 (6 : ZMod 927191293920799)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (1530018636833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (1530018636833, 1)] : List FactorBlock).map factorBlockValue).prod) = 927191293920799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_101
      · exact prime_sixtyFiveBK_1530018636833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 927191293920799) ^ 463595646960399 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 927191293920799) ^ 309063764640266 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 927191293920799) ^ 9180111820998 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 927191293920799) ^ 606 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1063012013816969 : Nat.Prime 1063012013816969 := by
  apply lucas_primality 1063012013816969 (3 : ZMod 1063012013816969)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (31, 1), (417491, 1), (446387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (31, 1), (417491, 1), (446387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063012013816969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_23
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_417491
      · exact prime_sixtyFiveBK_446387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1063012013816969) ^ 531506006908484 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063012013816969) ^ 46217913644216 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063012013816969) ^ 34290710123128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063012013816969) ^ 2546191448 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1063012013816969) ^ 2381368664 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1567136435847673 : Nat.Prime 1567136435847673 := by
  apply lucas_primality 1567136435847673 (5 : ZMod 1567136435847673)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (211, 1), (739, 1), (418763357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (211, 1), (739, 1), (418763357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1567136435847673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_211
      · exact prime_sixtyFiveBK_739
      · exact prime_sixtyFiveBK_418763357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1567136435847673) ^ 783568217923836 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1567136435847673) ^ 522378811949224 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1567136435847673) ^ 7427186899752 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1567136435847673) ^ 2120617639848 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1567136435847673) ^ 3742296 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1786373933899169 : Nat.Prime 1786373933899169 := by
  apply lucas_primality 1786373933899169 (3 : ZMod 1786373933899169)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2339039, 1), (23866291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2339039, 1), (23866291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1786373933899169 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_2339039
      · exact prime_sixtyFiveBK_23866291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1786373933899169) ^ 893186966949584 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1786373933899169) ^ 763721312 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1786373933899169) ^ 74849248 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2237821307367563 : Nat.Prime 2237821307367563 := by
  apply lucas_primality 2237821307367563 (2 : ZMod 2237821307367563)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (3262130185667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (3262130185667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2237821307367563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_3262130185667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2237821307367563) ^ 1118910653683781 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237821307367563) ^ 319688758195366 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2237821307367563) ^ 686 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2540470461941651 : Nat.Prime 2540470461941651 := by
  apply lucas_primality 2540470461941651 (2 : ZMod 2540470461941651)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1672301, 1), (4340419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1672301, 1), (4340419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2540470461941651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_1672301
      · exact prime_sixtyFiveBK_4340419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2540470461941651) ^ 1270235230970825 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540470461941651) ^ 508094092388330 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540470461941651) ^ 362924351705950 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540470461941651) ^ 1519146650 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540470461941651) ^ 585305350 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3068162970811819 : Nat.Prime 3068162970811819 := by
  apply lucas_primality 3068162970811819 (3 : ZMod 3068162970811819)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (112291, 1), (14275507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (112291, 1), (14275507, 1)] : List FactorBlock).map factorBlockValue).prod) = 3068162970811819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_112291
      · exact prime_sixtyFiveBK_14275507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3068162970811819) ^ 1534081485405909 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3068162970811819) ^ 1022720990270606 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3068162970811819) ^ 278923906437438 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3068162970811819) ^ 105798723131442 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3068162970811819) ^ 27323320398 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3068162970811819) ^ 214924974 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3180929520755957 : Nat.Prime 3180929520755957 := by
  apply lucas_primality 3180929520755957 (2 : ZMod 3180929520755957)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (795232380188989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (795232380188989, 1)] : List FactorBlock).map factorBlockValue).prod) = 3180929520755957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_795232380188989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3180929520755957) ^ 1590464760377978 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3180929520755957) ^ 4 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3267102831286793 : Nat.Prime 3267102831286793 := by
  apply lucas_primality 3267102831286793 (3 : ZMod 3267102831286793)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (6095341103147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (6095341103147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3267102831286793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_6095341103147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3267102831286793) ^ 1633551415643396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3267102831286793) ^ 48762728825176 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3267102831286793) ^ 536 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_3574545761033231 : Nat.Prime 3574545761033231 := by
  apply lucas_primality 3574545761033231 (23 : ZMod 3574545761033231)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (41, 1), (71, 1), (5867, 1), (565667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (41, 1), (71, 1), (5867, 1), (565667, 1)] : List FactorBlock).map factorBlockValue).prod) = 3574545761033231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_41
      · exact prime_sixtyFiveBK_71
      · exact prime_sixtyFiveBK_5867
      · exact prime_sixtyFiveBK_565667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 3574545761033231) ^ 1787272880516615 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 714909152206646 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 96609344892790 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 87184042952030 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 50345714944130 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 609262955690 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (23 : ZMod 3574545761033231) ^ 6319169690 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4526917323581449 : Nat.Prime 4526917323581449 := by
  apply lucas_primality 4526917323581449 (7 : ZMod 4526917323581449)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (2179, 1), (3049, 1), (230819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (2179, 1), (3049, 1), (230819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4526917323581449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_41
      · exact prime_sixtyFiveBK_2179
      · exact prime_sixtyFiveBK_3049
      · exact prime_sixtyFiveBK_230819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4526917323581449) ^ 2263458661790724 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4526917323581449) ^ 1508972441193816 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4526917323581449) ^ 110412617648328 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4526917323581449) ^ 2077520570712 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4526917323581449) ^ 1484721982152 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4526917323581449) ^ 19612411992 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_8654150840990257 : Nat.Prime 8654150840990257 := by
  apply lucas_primality 8654150840990257 (10 : ZMod 8654150840990257)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (31, 1), (70841, 1), (3909467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (31, 1), (70841, 1), (3909467, 1)] : List FactorBlock).map factorBlockValue).prod) = 8654150840990257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_70841
      · exact prime_sixtyFiveBK_3909467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8654150840990257) ^ 4327075420495128 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8654150840990257) ^ 2884716946996752 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8654150840990257) ^ 1236307262998608 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8654150840990257) ^ 279166156160976 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8654150840990257) ^ 122163024816 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 8654150840990257) ^ 2213639568 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_17783176784356463 : Nat.Prime 17783176784356463 := by
  apply lucas_primality 17783176784356463 (5 : ZMod 17783176784356463)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1067441, 1), (177230153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1067441, 1), (177230153, 1)] : List FactorBlock).map factorBlockValue).prod) = 17783176784356463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_1067441
      · exact prime_sixtyFiveBK_177230153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17783176784356463) ^ 8891588392178231 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17783176784356463) ^ 378365463496946 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17783176784356463) ^ 16659634382 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17783176784356463) ^ 100339454 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_22259612420131927 : Nat.Prime 22259612420131927 := by
  apply lucas_primality 22259612420131927 (6 : ZMod 22259612420131927)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (8982894439117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (8982894439117, 1)] : List FactorBlock).map factorBlockValue).prod) = 22259612420131927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_8982894439117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22259612420131927) ^ 11129806210065963 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 22259612420131927) ^ 7419870806710642 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 22259612420131927) ^ 3179944631447418 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 22259612420131927) ^ 377281566442914 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 22259612420131927) ^ 2478 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_24697779515990527 : Nat.Prime 24697779515990527 := by
  apply lucas_primality 24697779515990527 (5 : ZMod 24697779515990527)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (6079, 1), (3239874811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (6079, 1), (3239874811, 1)] : List FactorBlock).map factorBlockValue).prod) = 24697779515990527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_6079
      · exact prime_sixtyFiveBK_3239874811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24697779515990527) ^ 12348889757995263 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24697779515990527) ^ 8232593171996842 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24697779515990527) ^ 2245252683271866 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24697779515990527) ^ 1299883132420554 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24697779515990527) ^ 4062803012994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24697779515990527) ^ 7623066 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25447436166047657 : Nat.Prime 25447436166047657 := by
  apply lucas_primality 25447436166047657 (3 : ZMod 25447436166047657)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3180929520755957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3180929520755957, 1)] : List FactorBlock).map factorBlockValue).prod) = 25447436166047657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3180929520755957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 25447436166047657) ^ 12723718083023828 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 25447436166047657) ^ 8 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_39513360472743539 : Nat.Prime 39513360472743539 := by
  apply lucas_primality 39513360472743539 (2 : ZMod 39513360472743539)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (10313, 1), (6769280611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (10313, 1), (6769280611, 1)] : List FactorBlock).map factorBlockValue).prod) = 39513360472743539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_283
      · exact prime_sixtyFiveBK_10313
      · exact prime_sixtyFiveBK_6769280611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39513360472743539) ^ 19756680236371769 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39513360472743539) ^ 139623181882486 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39513360472743539) ^ 3831412825826 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39513360472743539) ^ 5837158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_119240202382050439 : Nat.Prime 119240202382050439 := by
  apply lucas_primality 119240202382050439 (3 : ZMod 119240202382050439)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (43, 1), (3950182282583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (43, 1), (3950182282583, 1)] : List FactorBlock).map factorBlockValue).prod) = 119240202382050439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_3950182282583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119240202382050439) ^ 59620101191025219 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119240202382050439) ^ 39746734127350146 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119240202382050439) ^ 9172323260157726 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119240202382050439) ^ 2773027962373266 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 119240202382050439) ^ 30186 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_127009848945544441 : Nat.Prime 127009848945544441 := by
  apply lucas_primality 127009848945544441 (11 : ZMod 127009848945544441)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (55706074098923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (55706074098923, 1)] : List FactorBlock).map factorBlockValue).prod) = 127009848945544441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_55706074098923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 127009848945544441) ^ 63504924472772220 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 127009848945544441) ^ 42336616315181480 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 127009848945544441) ^ 25401969789108888 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 127009848945544441) ^ 6684728891870760 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 127009848945544441) ^ 2280 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_128512761453882103 : Nat.Prime 128512761453882103 := by
  apply lucas_primality 128512761453882103 (3 : ZMod 128512761453882103)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (61, 1), (239, 1), (3106033451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (61, 1), (239, 1), (3106033451, 1)] : List FactorBlock).map factorBlockValue).prod) = 128512761453882103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_61
      · exact prime_sixtyFiveBK_239
      · exact prime_sixtyFiveBK_3106033451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128512761453882103) ^ 64256380726941051 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 42837587151294034 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 11682978313989282 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 2988668871020514 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 2106766581211182 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 537710298970218 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128512761453882103) ^ 41375202 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_151528160296014841 : Nat.Prime 151528160296014841 := by
  apply lucas_primality 151528160296014841 (7 : ZMod 151528160296014841)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13, 1), (73, 1), (19541, 1), (22697491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13, 1), (73, 1), (19541, 1), (22697491, 1)] : List FactorBlock).map factorBlockValue).prod) = 151528160296014841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_19541
      · exact prime_sixtyFiveBK_22697491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 151528160296014841) ^ 75764080148007420 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 50509386765338280 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 30305632059202968 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 11656012330462680 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 2075728223233080 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 7754370825240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 151528160296014841) ^ 6675987240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_152428227716499061 : Nat.Prime 152428227716499061 := by
  apply lucas_primality 152428227716499061 (11 : ZMod 152428227716499061)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2540470461941651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2540470461941651, 1)] : List FactorBlock).map factorBlockValue).prod) = 152428227716499061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_2540470461941651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 152428227716499061) ^ 76214113858249530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 152428227716499061) ^ 50809409238833020 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 152428227716499061) ^ 30485645543299812 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 152428227716499061) ^ 60 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_219334560204506881 : Nat.Prime 219334560204506881 := by
  apply lucas_primality 219334560204506881 (22 : ZMod 219334560204506881)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (7, 1), (337, 1), (84967, 1), (284969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (7, 1), (337, 1), (84967, 1), (284969, 1)] : List FactorBlock).map factorBlockValue).prod) = 219334560204506881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_337
      · exact prime_sixtyFiveBK_84967
      · exact prime_sixtyFiveBK_284969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 219334560204506881) ^ 109667280102253440 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 73111520068168960 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 43866912040901376 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 31333508600643840 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 650844392298240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 2581408784640 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (22 : ZMod 219334560204506881) ^ 769678667520 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_341548959196715443 : Nat.Prime 341548959196715443 := by
  apply lucas_primality 341548959196715443 (2 : ZMod 341548959196715443)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (859, 1), (82847, 1), (4789777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (859, 1), (82847, 1), (4789777, 1)] : List FactorBlock).map factorBlockValue).prod) = 341548959196715443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_167
      · exact prime_sixtyFiveBK_859
      · exact prime_sixtyFiveBK_82847
      · exact prime_sixtyFiveBK_4789777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 341548959196715443) ^ 170774479598357721 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 341548959196715443) ^ 113849653065571814 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 341548959196715443) ^ 2045203348483326 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 341548959196715443) ^ 397612292429238 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 341548959196715443) ^ 4122647279886 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 341548959196715443) ^ 71307904146 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_433708901637323353 : Nat.Prime 433708901637323353 := by
  apply lucas_primality 433708901637323353 (5 : ZMod 433708901637323353)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (1063012013816969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (1063012013816969, 1)] : List FactorBlock).map factorBlockValue).prod) = 433708901637323353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_1063012013816969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433708901637323353) ^ 216854450818661676 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 433708901637323353) ^ 144569633879107784 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 433708901637323353) ^ 25512288331607256 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 433708901637323353) ^ 408 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_839822657794212661 : Nat.Prime 839822657794212661 := by
  apply lucas_primality 839822657794212661 (2 : ZMod 839822657794212661)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 2), (42703, 1), (73017733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 2), (42703, 1), (73017733, 1)] : List FactorBlock).map factorBlockValue).prod) = 839822657794212661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_67
      · exact prime_sixtyFiveBK_42703
      · exact prime_sixtyFiveBK_73017733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 839822657794212661) ^ 419911328897106330 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 839822657794212661) ^ 279940885931404220 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 839822657794212661) ^ 167964531558842532 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 839822657794212661) ^ 12534666534241980 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 839822657794212661) ^ 19666596206220 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 839822657794212661) ^ 11501626020 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_890747486454447829 : Nat.Prime 890747486454447829 := by
  apply lucas_primality 890747486454447829 (2 : ZMod 890747486454447829)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (758969, 1), (32600785717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (758969, 1), (32600785717, 1)] : List FactorBlock).map factorBlockValue).prod) = 890747486454447829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_758969
      · exact prime_sixtyFiveBK_32600785717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 890747486454447829) ^ 445373743227223914 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 890747486454447829) ^ 296915828818149276 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 890747486454447829) ^ 1173628285812 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 890747486454447829) ^ 27322884 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1010602511033954093 : Nat.Prime 1010602511033954093 := by
  apply lucas_primality 1010602511033954093 (2 : ZMod 1010602511033954093)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5623, 1), (10223, 1), (4395152387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5623, 1), (10223, 1), (4395152387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1010602511033954093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5623
      · exact prime_sixtyFiveBK_10223
      · exact prime_sixtyFiveBK_4395152387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1010602511033954093) ^ 505301255516977046 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1010602511033954093) ^ 179726571409204 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1010602511033954093) ^ 98855767488404 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1010602511033954093) ^ 229935716 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1476942414922659539 : Nat.Prime 1476942414922659539 := by
  apply lucas_primality 1476942414922659539 (2 : ZMod 1476942414922659539)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1559, 1), (67668945978313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1559, 1), (67668945978313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1476942414922659539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_1559
      · exact prime_sixtyFiveBK_67668945978313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1476942414922659539) ^ 738471207461329769 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1476942414922659539) ^ 210991773560379934 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1476942414922659539) ^ 947365243696382 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1476942414922659539) ^ 21826 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2321601777705751241 : Nat.Prime 2321601777705751241 := by
  apply lucas_primality 2321601777705751241 (3 : ZMod 2321601777705751241)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (281, 1), (719, 1), (86539, 1), (474223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (281, 1), (719, 1), (86539, 1), (474223, 1)] : List FactorBlock).map factorBlockValue).prod) = 2321601777705751241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_281
      · exact prime_sixtyFiveBK_719
      · exact prime_sixtyFiveBK_86539
      · exact prime_sixtyFiveBK_474223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2321601777705751241) ^ 1160800888852875620 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 464320355541150248 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 331657396815107320 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 8261928034540040 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 3228931540619960 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 26827231395160 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2321601777705751241) ^ 4895590845880 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2399704274490609659 : Nat.Prime 2399704274490609659 := by
  apply lucas_primality 2399704274490609659 (2 : ZMod 2399704274490609659)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (19, 1), (139, 1), (1261823, 1), (2517821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (19, 1), (139, 1), (1261823, 1), (2517821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2399704274490609659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_19
      · exact prime_sixtyFiveBK_139
      · exact prime_sixtyFiveBK_1261823
      · exact prime_sixtyFiveBK_2517821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2399704274490609659) ^ 1199852137245304829 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 218154934044600878 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 184592636499277666 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 126300224973189982 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 17264059528709422 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 1901775664646 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399704274490609659) ^ 953087719298 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2685790277927939983 : Nat.Prime 2685790277927939983 := by
  apply lucas_primality 2685790277927939983 (3 : ZMod 2685790277927939983)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5074247, 1), (88216382251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5074247, 1), (88216382251, 1)] : List FactorBlock).map factorBlockValue).prod) = 2685790277927939983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5074247
      · exact prime_sixtyFiveBK_88216382251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2685790277927939983) ^ 1342895138963969991 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2685790277927939983) ^ 895263425975979994 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2685790277927939983) ^ 529298293506 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2685790277927939983) ^ 30445482 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4476304578003354961 : Nat.Prime 4476304578003354961 := by
  apply lucas_primality 4476304578003354961 (11 : ZMod 4476304578003354961)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (4149373, 1), (4494960823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (4149373, 1), (4494960823, 1)] : List FactorBlock).map factorBlockValue).prod) = 4476304578003354961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_4149373
      · exact prime_sixtyFiveBK_4494960823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4476304578003354961) ^ 2238152289001677480 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4476304578003354961) ^ 1492101526001118320 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4476304578003354961) ^ 895260915600670992 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4476304578003354961) ^ 1078790597520 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4476304578003354961) ^ 995849520 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4786319615413577161 : Nat.Prime 4786319615413577161 := by
  apply lucas_primality 4786319615413577161 (11 : ZMod 4786319615413577161)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (211, 1), (353, 1), (329957, 1), (1622953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (211, 1), (353, 1), (329957, 1), (1622953, 1)] : List FactorBlock).map factorBlockValue).prod) = 4786319615413577161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_211
      · exact prime_sixtyFiveBK_353
      · exact prime_sixtyFiveBK_329957
      · exact prime_sixtyFiveBK_1622953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4786319615413577161) ^ 2393159807706788580 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 1595439871804525720 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 957263923082715432 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 22683979219969560 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 13558979080491720 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 14505888995880 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4786319615413577161) ^ 2949142467720 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_7586589112186834751 : Nat.Prime 7586589112186834751 := by
  apply lucas_primality 7586589112186834751 (7 : ZMod 7586589112186834751)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 3), (11, 1), (13, 1), (79, 1), (3557, 1), (2201737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 3), (11, 1), (13, 1), (79, 1), (3557, 1), (2201737, 1)] : List FactorBlock).map factorBlockValue).prod) = 7586589112186834751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_79
      · exact prime_sixtyFiveBK_3557
      · exact prime_sixtyFiveBK_2201737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7586589112186834751) ^ 3793294556093417375 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 1517317822437366950 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 1083798444598119250 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 689689919289712250 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 583583777860525750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 96032773571985250 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 2132861712731750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 7586589112186834751) ^ 3445729036750 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_10676677398239407559 : Nat.Prime 10676677398239407559 := by
  apply lucas_primality 10676677398239407559 (7 : ZMod 10676677398239407559)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (7817, 1), (3466568502671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (7817, 1), (3466568502671, 1)] : List FactorBlock).map factorBlockValue).prod) = 10676677398239407559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_197
      · exact prime_sixtyFiveBK_7817
      · exact prime_sixtyFiveBK_3466568502671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10676677398239407559) ^ 5338338699119703779 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10676677398239407559) ^ 54196331970758414 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10676677398239407559) ^ 1365827990052374 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10676677398239407559) ^ 3079898 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_12899324364400226897 : Nat.Prime 12899324364400226897 := by
  apply lucas_primality 12899324364400226897 (5 : ZMod 12899324364400226897)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (28060997, 1), (200912911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (28060997, 1), (200912911, 1)] : List FactorBlock).map factorBlockValue).prod) = 12899324364400226897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_28060997
      · exact prime_sixtyFiveBK_200912911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12899324364400226897) ^ 6449662182200113448 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12899324364400226897) ^ 1172665851309111536 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12899324364400226897) ^ 992255720338478992 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12899324364400226897) ^ 459688740368 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12899324364400226897) ^ 64203561136 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_15821880388634959063 : Nat.Prime 15821880388634959063 := by
  apply lucas_primality 15821880388634959063 (3 : ZMod 15821880388634959063)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22133743, 1), (119138460439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22133743, 1), (119138460439, 1)] : List FactorBlock).map factorBlockValue).prod) = 15821880388634959063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_22133743
      · exact prime_sixtyFiveBK_119138460439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15821880388634959063) ^ 7910940194317479531 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15821880388634959063) ^ 5273960129544986354 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15821880388634959063) ^ 714830762634 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15821880388634959063) ^ 132802458 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_23349094004340440857 : Nat.Prime 23349094004340440857 := by
  apply lucas_primality 23349094004340440857 (10 : ZMod 23349094004340440857)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (59, 1), (140935668093223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (59, 1), (140935668093223, 1)] : List FactorBlock).map factorBlockValue).prod) = 23349094004340440857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_59
      · exact prime_sixtyFiveBK_140935668093223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 23349094004340440857) ^ 11674547002170220428 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 23349094004340440857) ^ 7783031334780146952 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 23349094004340440857) ^ 1796084154180033912 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 23349094004340440857) ^ 395747356005770184 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 23349094004340440857) ^ 165672 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25822255296972509611 : Nat.Prime 25822255296972509611 := by
  apply lucas_primality 25822255296972509611 (2 : ZMod 25822255296972509611)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (500583773, 1), (1719476119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (500583773, 1), (1719476119, 1)] : List FactorBlock).map factorBlockValue).prod) = 25822255296972509611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_500583773
      · exact prime_sixtyFiveBK_1719476119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25822255296972509611) ^ 12911127648486254805 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25822255296972509611) ^ 8607418432324169870 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25822255296972509611) ^ 5164451059394501922 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25822255296972509611) ^ 51584283570 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25822255296972509611) ^ 15017513190 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_97815169345036178731 : Nat.Prime 97815169345036178731 := by
  apply lucas_primality 97815169345036178731 (2 : ZMod 97815169345036178731)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (47, 1), (2237821307367563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (47, 1), (2237821307367563, 1)] : List FactorBlock).map factorBlockValue).prod) = 97815169345036178731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_2237821307367563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97815169345036178731) ^ 48907584672518089365 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97815169345036178731) ^ 32605056448345392910 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97815169345036178731) ^ 19563033869007235746 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97815169345036178731) ^ 3155328043388263830 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97815169345036178731) ^ 2081173815851833590 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97815169345036178731) ^ 43710 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_181038981678280263271 : Nat.Prime 181038981678280263271 := by
  apply lucas_primality 181038981678280263271 (13 : ZMod 181038981678280263271)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (47, 1), (433, 1), (830743, 1), (2766997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (47, 1), (433, 1), (830743, 1), (2766997, 1)] : List FactorBlock).map factorBlockValue).prod) = 181038981678280263271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_433
      · exact prime_sixtyFiveBK_830743
      · exact prime_sixtyFiveBK_2766997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 181038981678280263271) ^ 90519490839140131635 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 60346327226093421090 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 36207796335656052654 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 4210208876239075890 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 3851893227197452410 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 418103883783557190 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 217924173514890 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 181038981678280263271) ^ 65427964568910 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_453486890573255654917 : Nat.Prime 453486890573255654917 := by
  apply lucas_primality 453486890573255654917 (5 : ZMod 453486890573255654917)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (109, 1), (149, 1), (277, 1), (118313038169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (109, 1), (149, 1), (277, 1), (118313038169, 1)] : List FactorBlock).map factorBlockValue).prod) = 453486890573255654917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_71
      · exact prime_sixtyFiveBK_109
      · exact prime_sixtyFiveBK_149
      · exact prime_sixtyFiveBK_277
      · exact prime_sixtyFiveBK_118313038169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 453486890573255654917) ^ 226743445286627827458 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 151162296857751884972 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 6387139303848671196 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 4160430188745464724 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 3043536178343997684 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 1637136789073125108 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 453486890573255654917) ^ 3832940964 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1152585554109647011951 : Nat.Prime 1152585554109647011951 := by
  apply lucas_primality 1152585554109647011951 (3 : ZMod 1152585554109647011951)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (54617, 1), (140687033232589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (54617, 1), (140687033232589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152585554109647011951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_54617
      · exact prime_sixtyFiveBK_140687033232589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1152585554109647011951) ^ 576292777054823505975 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152585554109647011951) ^ 384195184703215670650 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152585554109647011951) ^ 230517110821929402390 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152585554109647011951) ^ 21103054984888350 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152585554109647011951) ^ 8192550 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1310405556752706859103 : Nat.Prime 1310405556752706859103 := by
  apply lucas_primality 1310405556752706859103 (5 : ZMod 1310405556752706859103)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (151, 1), (359, 1), (4733, 1), (66293, 1), (5503033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (151, 1), (359, 1), (4733, 1), (66293, 1), (5503033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1310405556752706859103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_151
      · exact prime_sixtyFiveBK_359
      · exact prime_sixtyFiveBK_4733
      · exact prime_sixtyFiveBK_66293
      · exact prime_sixtyFiveBK_5503033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1310405556752706859103) ^ 655202778376353429551 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 187200793821815265586 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 8678182495051038802 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 3650154754185812978 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 276865741971837494 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 19766876695167014 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1310405556752706859103) ^ 238124241078094 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1816740587432516736121 : Nat.Prime 1816740587432516736121 := by
  apply lucas_primality 1816740587432516736121 (11 : ZMod 1816740587432516736121)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (93056021, 1), (12514797937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (93056021, 1), (12514797937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1816740587432516736121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_93056021
      · exact prime_sixtyFiveBK_12514797937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1816740587432516736121) ^ 908370293716258368060 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1816740587432516736121) ^ 605580195810838912040 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1816740587432516736121) ^ 363348117486503347224 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1816740587432516736121) ^ 139749275956347441240 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1816740587432516736121) ^ 19523084781720 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1816740587432516736121) ^ 145167392760 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2827866046102521442873 : Nat.Prime 2827866046102521442873 := by
  apply lucas_primality 2827866046102521442873 (10 : ZMod 2827866046102521442873)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (277, 1), (3574545761033231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (277, 1), (3574545761033231, 1)] : List FactorBlock).map factorBlockValue).prod) = 2827866046102521442873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_277
      · exact prime_sixtyFiveBK_3574545761033231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2827866046102521442873) ^ 1413933023051260721436 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2827866046102521442873) ^ 942622015367507147624 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2827866046102521442873) ^ 403980863728931634696 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2827866046102521442873) ^ 166345061535442437816 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2827866046102521442873) ^ 10208902693510907736 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2827866046102521442873) ^ 791112 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4545300881900634778249 : Nat.Prime 4545300881900634778249 := by
  apply lucas_primality 4545300881900634778249 (7 : ZMod 4545300881900634778249)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4793, 1), (39513360472743539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4793, 1), (39513360472743539, 1)] : List FactorBlock).map factorBlockValue).prod) = 4545300881900634778249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_4793
      · exact prime_sixtyFiveBK_39513360472743539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4545300881900634778249) ^ 2272650440950317389124 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4545300881900634778249) ^ 1515100293966878259416 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4545300881900634778249) ^ 948320651345844936 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4545300881900634778249) ^ 115032 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_10994958235841832157813 : Nat.Prime 10994958235841832157813 := by
  apply lucas_primality 10994958235841832157813 (2 : ZMod 10994958235841832157813)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1091, 1), (839822657794212661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1091, 1), (839822657794212661, 1)] : List FactorBlock).map factorBlockValue).prod) = 10994958235841832157813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_1091
      · exact prime_sixtyFiveBK_839822657794212661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10994958235841832157813) ^ 5497479117920916078906 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10994958235841832157813) ^ 3664986078613944052604 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10994958235841832157813) ^ 10077871893530551932 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10994958235841832157813) ^ 13092 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_19711341983884478927563 : Nat.Prime 19711341983884478927563 := by
  apply lucas_primality 19711341983884478927563 (2 : ZMod 19711341983884478927563)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (29, 2), (31, 1), (733, 1), (3370800906839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (29, 2), (31, 1), (733, 1), (3370800906839, 1)] : List FactorBlock).map factorBlockValue).prod) = 19711341983884478927563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_29
      · exact prime_sixtyFiveBK_31
      · exact prime_sixtyFiveBK_733
      · exact prime_sixtyFiveBK_3370800906839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19711341983884478927563) ^ 9855670991942239463781 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 6570447327961492975854 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 1159490704934381113386 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 679701447720154445778 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 635849741415628352502 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 26891326035313068114 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19711341983884478927563) ^ 5847673158 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_29330522493177965657959 : Nat.Prime 29330522493177965657959 := by
  apply lucas_primality 29330522493177965657959 (7 : ZMod 29330522493177965657959)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (21162871, 1), (25665601985087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (21162871, 1), (25665601985087, 1)] : List FactorBlock).map factorBlockValue).prod) = 29330522493177965657959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_21162871
      · exact prime_sixtyFiveBK_25665601985087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29330522493177965657959) ^ 14665261246588982828979 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 29330522493177965657959) ^ 9776840831059321885986 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 29330522493177965657959) ^ 1385942507194698 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 29330522493177965657959) ^ 1142795034 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_72701129358252926724229 : Nat.Prime 72701129358252926724229 := by
  apply lucas_primality 72701129358252926724229 (6 : ZMod 72701129358252926724229)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (269, 1), (541, 1), (9773209, 1), (608520397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (269, 1), (541, 1), (9773209, 1), (608520397, 1)] : List FactorBlock).map factorBlockValue).prod) = 72701129358252926724229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_269
      · exact prime_sixtyFiveBK_541
      · exact prime_sixtyFiveBK_9773209
      · exact prime_sixtyFiveBK_608520397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 72701129358252926724229) ^ 36350564679126463362114 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 24233709786084308908076 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 10385875622607560960604 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 270264421406144709012 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 134382863878471213908 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 7438818647821092 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 72701129358252926724229) ^ 119471967935124 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_202693389532070575574771 : Nat.Prime 202693389532070575574771 := by
  apply lucas_primality 202693389532070575574771 (2 : ZMod 202693389532070575574771)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1609, 1), (3298111, 1), (3819603416323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1609, 1), (3298111, 1), (3819603416323, 1)] : List FactorBlock).map factorBlockValue).prod) = 202693389532070575574771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_1609
      · exact prime_sixtyFiveBK_3298111
      · exact prime_sixtyFiveBK_3819603416323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 202693389532070575574771) ^ 101346694766035287787385 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 202693389532070575574771) ^ 40538677906414115114954 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 202693389532070575574771) ^ 125974760430124658530 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 202693389532070575574771) ^ 61457418968637070 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 202693389532070575574771) ^ 53066605990 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_203674341624636433093223 : Nat.Prime 203674341624636433093223 := by
  apply lucas_primality 203674341624636433093223 (5 : ZMod 203674341624636433093223)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (769, 1), (643037567, 1), (12114199421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (769, 1), (643037567, 1), (12114199421, 1)] : List FactorBlock).map factorBlockValue).prod) = 203674341624636433093223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_769
      · exact prime_sixtyFiveBK_643037567
      · exact prime_sixtyFiveBK_12114199421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 203674341624636433093223) ^ 101837170812318216546611 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203674341624636433093223) ^ 11980843624978613711366 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203674341624636433093223) ^ 264856100942310056038 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203674341624636433093223) ^ 316737858061466 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 203674341624636433093223) ^ 16812860226782 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_257729977753239592810271 : Nat.Prime 257729977753239592810271 := by
  apply lucas_primality 257729977753239592810271 (19 : ZMod 257729977753239592810271)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4302758197, 1), (5989878258391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4302758197, 1), (5989878258391, 1)] : List FactorBlock).map factorBlockValue).prod) = 257729977753239592810271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_4302758197
      · exact prime_sixtyFiveBK_5989878258391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 257729977753239592810271) ^ 128864988876619796405135 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (19 : ZMod 257729977753239592810271) ^ 51545995550647918562054 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (19 : ZMod 257729977753239592810271) ^ 59898782583910 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (19 : ZMod 257729977753239592810271) ^ 43027581970 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_538757886865235416847113 : Nat.Prime 538757886865235416847113 := by
  apply lucas_primality 538757886865235416847113 (5 : ZMod 538757886865235416847113)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (358997707, 1), (1454193733763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (358997707, 1), (1454193733763, 1)] : List FactorBlock).map factorBlockValue).prod) = 538757886865235416847113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_43
      · exact prime_sixtyFiveBK_358997707
      · exact prime_sixtyFiveBK_1454193733763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 538757886865235416847113) ^ 269378943432617708423556 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 538757886865235416847113) ^ 179585962288411805615704 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 538757886865235416847113) ^ 12529253182912451554584 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 538757886865235416847113) ^ 1500727933243416 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 538757886865235416847113) ^ 370485633624 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_576226895515873588538339 : Nat.Prime 576226895515873588538339 := by
  apply lucas_primality 576226895515873588538339 (2 : ZMod 576226895515873588538339)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (9337, 1), (27635141, 1), (65681878421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (9337, 1), (27635141, 1), (65681878421, 1)] : List FactorBlock).map factorBlockValue).prod) = 576226895515873588538339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_9337
      · exact prime_sixtyFiveBK_27635141
      · exact prime_sixtyFiveBK_65681878421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 576226895515873588538339) ^ 288113447757936794269169 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 576226895515873588538339) ^ 33895699736227858149314 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 576226895515873588538339) ^ 61714351024512540274 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 576226895515873588538339) ^ 20851237759773818 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 576226895515873588538339) ^ 8772996591578 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_598294567801403330542793 : Nat.Prime 598294567801403330542793 := by
  apply lucas_primality 598294567801403330542793 (3 : ZMod 598294567801403330542793)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (359, 1), (54775001, 1), (39208163063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (359, 1), (54775001, 1), (39208163063, 1)] : List FactorBlock).map factorBlockValue).prod) = 598294567801403330542793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_97
      · exact prime_sixtyFiveBK_359
      · exact prime_sixtyFiveBK_54775001
      · exact prime_sixtyFiveBK_39208163063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 598294567801403330542793) ^ 299147283900701665271396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 598294567801403330542793) ^ 6167985235066013716936 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 598294567801403330542793) ^ 1666558684683574736888 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 598294567801403330542793) ^ 10922766898742792 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 598294567801403330542793) ^ 15259438878584 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1083287718556554918849131 : Nat.Prime 1083287718556554918849131 := by
  apply lucas_primality 1083287718556554918849131 (2 : ZMod 1083287718556554918849131)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (1741, 1), (4786319615413577161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (1741, 1), (4786319615413577161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083287718556554918849131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_1741
      · exact prime_sixtyFiveBK_4786319615413577161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1083287718556554918849131) ^ 541643859278277459424565 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083287718556554918849131) ^ 216657543711310983769826 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083287718556554918849131) ^ 83329824504350378373010 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083287718556554918849131) ^ 622221550003765030930 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1083287718556554918849131) ^ 226330 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1587328764312962414810867 : Nat.Prime 1587328764312962414810867 := by
  apply lucas_primality 1587328764312962414810867 (2 : ZMod 1587328764312962414810867)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5851, 1), (3200401, 1), (42384044316683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5851, 1), (3200401, 1), (42384044316683, 1)] : List FactorBlock).map factorBlockValue).prod) = 1587328764312962414810867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5851
      · exact prime_sixtyFiveBK_3200401
      · exact prime_sixtyFiveBK_42384044316683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1587328764312962414810867) ^ 793664382156481207405433 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1587328764312962414810867) ^ 271291875630313179766 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1587328764312962414810867) ^ 495978086593824466 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1587328764312962414810867) ^ 37451092502 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_7492185577330939786315541 : Nat.Prime 7492185577330939786315541 := by
  apply lucas_primality 7492185577330939786315541 (2 : ZMod 7492185577330939786315541)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (257, 1), (12899324364400226897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (257, 1), (12899324364400226897, 1)] : List FactorBlock).map factorBlockValue).prod) = 7492185577330939786315541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_113
      · exact prime_sixtyFiveBK_257
      · exact prime_sixtyFiveBK_12899324364400226897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7492185577330939786315541) ^ 3746092788665469893157770 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7492185577330939786315541) ^ 1498437115466187957263108 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7492185577330939786315541) ^ 66302527233017166250580 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7492185577330939786315541) ^ 29152473063544512787220 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7492185577330939786315541) ^ 580820 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_25607246739981156077387039 : Nat.Prime 25607246739981156077387039 := by
  apply lucas_primality 25607246739981156077387039 (7 : ZMod 25607246739981156077387039)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (13768443217, 1), (25133115589811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (13768443217, 1), (25133115589811, 1)] : List FactorBlock).map factorBlockValue).prod) = 25607246739981156077387039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_13768443217
      · exact prime_sixtyFiveBK_25133115589811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 25607246739981156077387039) ^ 12803623369990578038693519 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25607246739981156077387039) ^ 692087749729220434523974 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25607246739981156077387039) ^ 1859850553646014 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (7 : ZMod 25607246739981156077387039) ^ 1018864798058 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_39920699982692700980903119 : Nat.Prime 39920699982692700980903119 := by
  apply lucas_primality 39920699982692700980903119 (3 : ZMod 39920699982692700980903119)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (6719, 1), (92503, 1), (1500407, 1), (151802701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (6719, 1), (92503, 1), (1500407, 1), (151802701, 1)] : List FactorBlock).map factorBlockValue).prod) = 39920699982692700980903119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_47
      · exact prime_sixtyFiveBK_6719
      · exact prime_sixtyFiveBK_92503
      · exact prime_sixtyFiveBK_1500407
      · exact prime_sixtyFiveBK_151802701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39920699982692700980903119) ^ 19960349991346350490451559 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 13306899994230900326967706 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 849376595376440446402194 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 5941464501070501708722 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 431561138370568532706 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 26606580736222039074 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 39920699982692700980903119) ^ 262977534126304518 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_41539106738747810480128921 : Nat.Prime 41539106738747810480128921 := by
  apply lucas_primality 41539106738747810480128921 (13 : ZMod 41539106738747810480128921)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (4444357, 1), (8654150840990257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (4444357, 1), (8654150840990257, 1)] : List FactorBlock).map factorBlockValue).prod) = 41539106738747810480128921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_4444357
      · exact prime_sixtyFiveBK_8654150840990257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 41539106738747810480128921) ^ 20769553369373905240064460 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41539106738747810480128921) ^ 13846368912915936826709640 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41539106738747810480128921) ^ 8307821347749562096025784 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41539106738747810480128921) ^ 9346482908269477560 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (13 : ZMod 41539106738747810480128921) ^ 4799905560 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_43588966231811372313237949 : Nat.Prime 43588966231811372313237949 := by
  apply lucas_primality 43588966231811372313237949 (2 : ZMod 43588966231811372313237949)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (62807769337, 1), (6425981107813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (62807769337, 1), (6425981107813, 1)] : List FactorBlock).map factorBlockValue).prod) = 43588966231811372313237949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_62807769337
      · exact prime_sixtyFiveBK_6425981107813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43588966231811372313237949) ^ 21794483115905686156618974 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43588966231811372313237949) ^ 14529655410603790771079316 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43588966231811372313237949) ^ 694005959643804 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43588966231811372313237949) ^ 6783239088396 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_91484937460337439747902981 : Nat.Prime 91484937460337439747902981 := by
  apply lucas_primality 91484937460337439747902981 (2 : ZMod 91484937460337439747902981)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1249, 1), (17558861, 1), (208574312439841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1249, 1), (17558861, 1), (208574312439841, 1)] : List FactorBlock).map factorBlockValue).prod) = 91484937460337439747902981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_1249
      · exact prime_sixtyFiveBK_17558861
      · exact prime_sixtyFiveBK_208574312439841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91484937460337439747902981) ^ 45742468730168719873951490 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 91484937460337439747902981) ^ 18296987492067487949580596 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 91484937460337439747902981) ^ 73246547206034779622020 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 91484937460337439747902981) ^ 5210186324747228180 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 91484937460337439747902981) ^ 438620347780 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_165263112831577310512340869 : Nat.Prime 165263112831577310512340869 := by
  apply lucas_primality 165263112831577310512340869 (6 : ZMod 165263112831577310512340869)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (28087, 1), (23349094004340440857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (28087, 1), (23349094004340440857, 1)] : List FactorBlock).map factorBlockValue).prod) = 165263112831577310512340869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_7
      · exact prime_sixtyFiveBK_28087
      · exact prime_sixtyFiveBK_23349094004340440857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 165263112831577310512340869) ^ 82631556415788655256170434 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 165263112831577310512340869) ^ 55087704277192436837446956 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 165263112831577310512340869) ^ 23609016118796758644620124 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 165263112831577310512340869) ^ 5883971689093791095964 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (6 : ZMod 165263112831577310512340869) ^ 7077924 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_259619417117173815500805757 : Nat.Prime 259619417117173815500805757 := by
  apply lucas_primality 259619417117173815500805757 (2 : ZMod 259619417117173815500805757)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (631, 1), (1163, 1), (214147, 1), (137668587273043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (631, 1), (1163, 1), (214147, 1), (137668587273043, 1)] : List FactorBlock).map factorBlockValue).prod) = 259619417117173815500805757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_631
      · exact prime_sixtyFiveBK_1163
      · exact prime_sixtyFiveBK_214147
      · exact prime_sixtyFiveBK_137668587273043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259619417117173815500805757) ^ 129809708558586907750402878 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 259619417117173815500805757) ^ 86539805705724605166935252 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 259619417117173815500805757) ^ 411441231564459295563876 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 259619417117173815500805757) ^ 223232516867733289338612 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 259619417117173815500805757) ^ 1212342069313013096148 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 259619417117173815500805757) ^ 1885829020692 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_415391067387478104801289211 : Nat.Prime 415391067387478104801289211 := by
  apply lucas_primality 415391067387478104801289211 (2 : ZMod 415391067387478104801289211)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41539106738747810480128921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41539106738747810480128921, 1)] : List FactorBlock).map factorBlockValue).prod) = 415391067387478104801289211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_5
      · exact prime_sixtyFiveBK_41539106738747810480128921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 415391067387478104801289211) ^ 207695533693739052400644605 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 415391067387478104801289211) ^ 83078213477495620960257842 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 415391067387478104801289211) ^ 10 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1219799166137832529972039747 : Nat.Prime 1219799166137832529972039747 := by
  apply lucas_primality 1219799166137832529972039747 (2 : ZMod 1219799166137832529972039747)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (37, 1), (148793, 1), (394579, 1), (570643, 1), (1146881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (37, 1), (148793, 1), (394579, 1), (570643, 1), (1146881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1219799166137832529972039747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_11
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_37
      · exact prime_sixtyFiveBK_148793
      · exact prime_sixtyFiveBK_394579
      · exact prime_sixtyFiveBK_570643
      · exact prime_sixtyFiveBK_1146881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1219799166137832529972039747) ^ 609899583068916264986019873 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 406599722045944176657346582 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 110890833285257502724730886 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 93830705087525579228618442 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 32967545030752230539784858 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 8197960698002140759122 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 3091394032976495277174 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 2137587188728911999222 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1219799166137832529972039747) ^ 1063579539758556057666 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_1449949952201574516759217057 : Nat.Prime 1449949952201574516759217057 := by
  apply lucas_primality 1449949952201574516759217057 (15 : ZMod 1449949952201574516759217057)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (73, 1), (8377241, 1), (24697779515990527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (73, 1), (8377241, 1), (24697779515990527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449949952201574516759217057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_73
      · exact prime_sixtyFiveBK_8377241
      · exact prime_sixtyFiveBK_24697779515990527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 1449949952201574516759217057) ^ 724974976100787258379608528 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 1449949952201574516759217057) ^ 483316650733858172253072352 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 1449949952201574516759217057) ^ 19862328112350335846016672 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 1449949952201574516759217057) ^ 173082038848061613216 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (15 : ZMod 1449949952201574516759217057) ^ 58707704928 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2022298617544301299690486949 : Nat.Prime 2022298617544301299690486949 := by
  apply lucas_primality 2022298617544301299690486949 (2 : ZMod 2022298617544301299690486949)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (109, 1), (18882149927, 1), (18895744228343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (109, 1), (18882149927, 1), (18895744228343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2022298617544301299690486949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_13
      · exact prime_sixtyFiveBK_109
      · exact prime_sixtyFiveBK_18882149927
      · exact prime_sixtyFiveBK_18895744228343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2022298617544301299690486949) ^ 1011149308772150649845243474 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2022298617544301299690486949) ^ 155561432118792407668498996 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2022298617544301299690486949) ^ 18553198326094507336609972 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2022298617544301299690486949) ^ 107101078286248124 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2022298617544301299690486949) ^ 107024025786236 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_2561578248889448312941283467 : Nat.Prime 2561578248889448312941283467 := by
  apply lucas_primality 2561578248889448312941283467 (2 : ZMod 2561578248889448312941283467)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2417, 1), (491882411, 1), (359102503615253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2417, 1), (491882411, 1), (359102503615253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2561578248889448312941283467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_3
      · exact prime_sixtyFiveBK_2417
      · exact prime_sixtyFiveBK_491882411
      · exact prime_sixtyFiveBK_359102503615253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2561578248889448312941283467) ^ 1280789124444724156470641733 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2561578248889448312941283467) ^ 853859416296482770980427822 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2561578248889448312941283467) ^ 1059817231646441172089898 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2561578248889448312941283467) ^ 5207704507428399006 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2561578248889448312941283467) ^ 7133278724322 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_4269297081482413854902139113 : Nat.Prime 4269297081482413854902139113 := by
  apply lucas_primality 4269297081482413854902139113 (3 : ZMod 4269297081482413854902139113)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11813, 1), (334253083, 1), (135154578931291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11813, 1), (334253083, 1), (135154578931291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4269297081482413854902139113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_11813
      · exact prime_sixtyFiveBK_334253083
      · exact prime_sixtyFiveBK_135154578931291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4269297081482413854902139113) ^ 2134648540741206927451069556 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269297081482413854902139113) ^ 361406677514806895361224 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269297081482413854902139113) ^ 12772648327322724664 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269297081482413854902139113) ^ 31588253355832 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem prime_sixtyFiveBK_6986122496971222671658045823 : Nat.Prime 6986122496971222671658045823 := by
  apply lucas_primality 6986122496971222671658045823 (5 : ZMod 6986122496971222671658045823)
  · rw [← sixtyFiveBKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (114400141, 1), (17783176784356463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (114400141, 1), (17783176784356463, 1)] : List FactorBlock).map factorBlockValue).prod) = 6986122496971222671658045823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyFiveBK_2
      · exact prime_sixtyFiveBK_17
      · exact prime_sixtyFiveBK_101
      · exact prime_sixtyFiveBK_114400141
      · exact prime_sixtyFiveBK_17783176784356463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6986122496971222671658045823) ^ 3493061248485611335829022911 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6986122496971222671658045823) ^ 410948382174777804215179166 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6986122496971222671658045823) ^ 69169529672982402689683622 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6986122496971222671658045823) ^ 61067429077480093942 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide
    · change (5 : ZMod 6986122496971222671658045823) ^ 392850084194 ≠ 1
      rw [← sixtyFiveBKFastPow_eq_pow]
      decide

private theorem phi_sixtyFiveBK_76847347466683449388238504000 : Nat.totient 76847347466683449388238504000 = 30738642074239414168240128000 := by
  rw [← show ((([(2, 6), (5, 3), (103681, 1), (70452007, 1), (1315062360739, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_103681, prime_sixtyFiveBK_70452007, prime_sixtyFiveBK_1315062360739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504001 : Nat.totient 76847347466683449388238504001 = 50023106989398761487248637840 := by
  rw [← show ((([(3, 1), (43, 1), (2939, 1), (202693389532070575574771, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_43, prime_sixtyFiveBK_2939, prime_sixtyFiveBK_202693389532070575574771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504002 : Nat.totient 76847347466683449388238504002 = 38423673635526555348690254100 := by
  rw [← show ((([(2, 1), (392819171, 1), (97815169345036178731, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_392819171, prime_sixtyFiveBK_97815169345036178731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504003 : Nat.totient 76847347466683449388238504003 = 76819728253768414757985542400 := by
  rw [← show ((([(3389, 1), (18539, 1), (96451, 1), (24624967, 1), (514977929, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3389, prime_sixtyFiveBK_18539, prime_sixtyFiveBK_96451, prime_sixtyFiveBK_24624967, prime_sixtyFiveBK_514977929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504004 : Nat.totient 76847347466683449388238504004 = 25422182745847832190845491200 := by
  rw [← show ((([(2, 2), (3, 1), (241, 1), (307, 1), (6029, 1), (937043059, 1), (15321009631, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_241, prime_sixtyFiveBK_307, prime_sixtyFiveBK_6029, prime_sixtyFiveBK_937043059, prime_sixtyFiveBK_15321009631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504005 : Nat.totient 76847347466683449388238504005 = 48670614260695608386186188800 := by
  rw [← show ((([(5, 1), (7, 1), (19, 1), (41, 1), (1663, 1), (11119, 1), (152428227716499061, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_7, prime_sixtyFiveBK_19, prime_sixtyFiveBK_41, prime_sixtyFiveBK_1663, prime_sixtyFiveBK_11119, prime_sixtyFiveBK_152428227716499061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504006 : Nat.totient 76847347466683449388238504006 = 37505056435822904114105462400 := by
  rw [← show ((([(2, 1), (61, 1), (131, 1), (175859, 1), (6673613, 1), (4097058239699, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_61, prime_sixtyFiveBK_131, prime_sixtyFiveBK_175859, prime_sixtyFiveBK_6673613, prime_sixtyFiveBK_4097058239699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504007 : Nat.totient 76847347466683449388238504007 = 50600589925355404470745896960 := by
  rw [← show ((([(3, 2), (83, 1), (6091, 1), (9619, 1), (323233, 1), (5432178877733, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_83, prime_sixtyFiveBK_6091, prime_sixtyFiveBK_9619, prime_sixtyFiveBK_323233, prime_sixtyFiveBK_5432178877733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504008 : Nat.totient 76847347466683449388238504008 = 36040032859648250472890649600 := by
  rw [← show ((([(2, 3), (17, 1), (293, 1), (21726314131, 1), (88763884235591, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_17, prime_sixtyFiveBK_293, prime_sixtyFiveBK_21726314131, prime_sixtyFiveBK_88763884235591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504009 : Nat.totient 76847347466683449388238504009 = 69850392092526661167391902400 := by
  rw [← show ((([(11, 1), (6449, 1), (1083287718556554918849131, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_11, prime_sixtyFiveBK_6449, prime_sixtyFiveBK_1083287718556554918849131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504010 : Nat.totient 76847347466683449388238504010 = 20492625991115586503530267728 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (2561578248889448312941283467, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_2561578248889448312941283467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504011 : Nat.totient 76847347466683449388238504011 = 70936012781863041918521975040 := by
  rw [← show ((([(13, 1), (309619603, 1), (2907694969, 1), (6566111221, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_13, prime_sixtyFiveBK_309619603, prime_sixtyFiveBK_2907694969, prime_sixtyFiveBK_6566111221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504012 : Nat.totient 76847347466683449388238504012 = 32934522942110895501620488320 := by
  rw [← show ((([(2, 2), (7, 1), (603821, 1), (4545300881900634778249, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_7, prime_sixtyFiveBK_603821, prime_sixtyFiveBK_4545300881900634778249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504013 : Nat.totient 76847347466683449388238504013 = 50880364027390457402196480000 := by
  rw [← show ((([(3, 1), (251, 1), (347, 1), (1340903, 1), (219334560204506881, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_251, prime_sixtyFiveBK_347, prime_sixtyFiveBK_1340903, prime_sixtyFiveBK_219334560204506881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504014 : Nat.totient 76847347466683449388238504014 = 37850002353070995000034344960 := by
  rw [← show ((([(2, 1), (67, 1), (206033, 1), (12189982081, 1), (228341174077, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_67, prime_sixtyFiveBK_206033, prime_sixtyFiveBK_12189982081, prime_sixtyFiveBK_228341174077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504015 : Nat.totient 76847347466683449388238504015 = 60388627594338203866407950112 := by
  rw [← show ((([(5, 1), (59, 1), (1279, 1), (203674341624636433093223, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_59, prime_sixtyFiveBK_1279, prime_sixtyFiveBK_203674341624636433093223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504016 : Nat.totient 76847347466683449388238504016 = 25613613972199802230417601280 := by
  rw [← show ((([(2, 4), (3, 2), (11813, 1), (334253083, 1), (135154578931291, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_11813, prime_sixtyFiveBK_334253083, prime_sixtyFiveBK_135154578931291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504017 : Nat.totient 76847347466683449388238504017 = 76845943918173338341356565440 := by
  rw [← show ((([(73517, 1), (214559, 1), (1067333599, 1), (4564510261, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_73517, prime_sixtyFiveBK_214559, prime_sixtyFiveBK_1067333599, prime_sixtyFiveBK_4564510261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504018 : Nat.totient 76847347466683449388238504018 = 37098719463336042692360758032 := by
  rw [← show ((([(2, 1), (29, 1), (11111640539, 1), (119240202382050439, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_29, prime_sixtyFiveBK_11111640539, prime_sixtyFiveBK_119240202382050439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504019 : Nat.totient 76847347466683449388238504019 = 43912503330670314004571506656 := by
  rw [← show ((([(3, 1), (7, 3), (164683, 1), (453486890573255654917, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_7, prime_sixtyFiveBK_164683, prime_sixtyFiveBK_453486890573255654917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504020 : Nat.totient 76847347466683449388238504020 = 26628217088638245380793292800 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (23, 1), (509, 1), (547, 1), (2286149, 1), (23859905755271, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_11, prime_sixtyFiveBK_23, prime_sixtyFiveBK_509, prime_sixtyFiveBK_547, prime_sixtyFiveBK_2286149, prime_sixtyFiveBK_23859905755271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504021 : Nat.totient 76847347466683449388238504021 = 75397397514481874871479286912 := by
  rw [← show ((([(53, 1), (1449949952201574516759217057, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_53, prime_sixtyFiveBK_1449949952201574516759217057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504022 : Nat.totient 76847347466683449388238504022 = 25615627483691168759252096064 := by
  rw [← show ((([(2, 1), (3, 1), (165463, 1), (133102327, 1), (581555394718537, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_165463, prime_sixtyFiveBK_133102327, prime_sixtyFiveBK_581555394718537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504023 : Nat.totient 76847347466683449388238504023 = 74368400546612116355145735000 := by
  rw [← show ((([(31, 1), (326753783, 1), (7586589112186834751, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_31, prime_sixtyFiveBK_326753783, prime_sixtyFiveBK_7586589112186834751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504024 : Nat.totient 76847347466683449388238504024 = 33293000809860628164039995904 := by
  rw [← show ((([(2, 3), (13, 1), (19, 1), (109, 1), (18882149927, 1), (18895744228343, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_13, prime_sixtyFiveBK_19, prime_sixtyFiveBK_109, prime_sixtyFiveBK_18882149927, prime_sixtyFiveBK_18895744228343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504025 : Nat.totient 76847347466683449388238504025 = 38434278641946155665566105600 := by
  rw [← show ((([(3, 3), (5, 2), (17, 1), (283, 1), (10193, 1), (2321601777705751241, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_17, prime_sixtyFiveBK_283, prime_sixtyFiveBK_10193, prime_sixtyFiveBK_2321601777705751241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504026 : Nat.totient 76847347466683449388238504026 = 32934569623288137792978785424 := by
  rw [← show ((([(2, 1), (7, 1), (4188853, 1), (1310405556752706859103, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_7, prime_sixtyFiveBK_4188853, prime_sixtyFiveBK_1310405556752706859103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504027 : Nat.totient 76847347466683449388238504027 = 76821187232361822729941601000 := by
  rw [← show ((([(3467, 1), (19231, 1), (1152585554109647011951, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3467, prime_sixtyFiveBK_19231, prime_sixtyFiveBK_1152585554109647011951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504028 : Nat.totient 76847347466683449388238504028 = 25539419226470365030283182080 := by
  rw [← show ((([(2, 2), (3, 1), (461, 1), (1229, 1), (25285546369, 1), (447015399829, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_461, prime_sixtyFiveBK_1229, prime_sixtyFiveBK_25285546369, prime_sixtyFiveBK_447015399829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504029 : Nat.totient 76847347466683449388238504029 = 76847347465206506921284467580 := by
  rw [← show ((([(52031376911, 1), (1476942414922659539, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_52031376911, prime_sixtyFiveBK_1476942414922659539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504030 : Nat.totient 76847347466683449388238504030 = 30084912220757896786852711680 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (4467017, 1), (577449871, 1), (63386844107, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_47, prime_sixtyFiveBK_4467017, prime_sixtyFiveBK_577449871, prime_sixtyFiveBK_63386844107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504031 : Nat.totient 76847347466683449388238504031 = 45984321356720680480790786400 := by
  rw [← show ((([(3, 1), (11, 1), (79, 1), (162823, 1), (181038981678280263271, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_11, prime_sixtyFiveBK_79, prime_sixtyFiveBK_162823, prime_sixtyFiveBK_181038981678280263271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504032 : Nat.totient 76847347466683449388238504032 = 38422778939790838631197286400 := by
  rw [← show ((([(2, 5), (51257, 1), (265231, 1), (142977433, 1), (1235474941, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_51257, prime_sixtyFiveBK_265231, prime_sixtyFiveBK_142977433, prime_sixtyFiveBK_1235474941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504033 : Nat.totient 76847347466683449388238504033 = 65752157235546866329998861888 := by
  rw [← show ((([(7, 1), (563, 1), (106576237, 1), (203626223, 1), (898521263, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_7, prime_sixtyFiveBK_563, prime_sixtyFiveBK_106576237, prime_sixtyFiveBK_203626223, prime_sixtyFiveBK_898521263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504034 : Nat.totient 76847347466683449388238504034 = 25615782488894483129412834672 := by
  rw [← show ((([(2, 1), (3, 2), (4269297081482413854902139113, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_4269297081482413854902139113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504035 : Nat.totient 76847347466683449388238504035 = 59816313703796847091385646240 := by
  rw [← show ((([(5, 1), (37, 1), (415391067387478104801289211, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_37, prime_sixtyFiveBK_415391067387478104801289211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504036 : Nat.totient 76847347466683449388238504036 = 37882495229625666366536512800 := by
  rw [← show ((([(2, 2), (71, 1), (88192594141, 1), (3068162970811819, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_71, prime_sixtyFiveBK_88192594141, prime_sixtyFiveBK_3068162970811819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504037 : Nat.totient 76847347466683449388238504037 = 47110862910256949376352115520 := by
  rw [← show ((([(3, 1), (13, 1), (263, 1), (7492185577330939786315541, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_13, prime_sixtyFiveBK_263, prime_sixtyFiveBK_7492185577330939786315541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504038 : Nat.totient 76847347466683449388238504038 = 38177221744485330026298401376 := by
  rw [← show ((([(2, 1), (157, 1), (22259, 1), (10994958235841832157813, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_157, prime_sixtyFiveBK_22259, prime_sixtyFiveBK_10994958235841832157813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504039 : Nat.totient 76847347466683449388238504039 = 76821740219943468232161114000 := by
  rw [← show ((([(3001, 1), (25607246739981156077387039, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3001, prime_sixtyFiveBK_25607246739981156077387039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504040 : Nat.totient 76847347466683449388238504040 = 17565107992384788431597372160 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (7, 1), (91484937460337439747902981, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_7, prime_sixtyFiveBK_91484937460337439747902981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504041 : Nat.totient 76847347466683449388238504041 = 75762330206723684630346240000 := by
  rw [← show ((([(73, 1), (4951, 1), (6781, 1), (13469, 1), (370871, 1), (6277129993, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_73, prime_sixtyFiveBK_4951, prime_sixtyFiveBK_6781, prime_sixtyFiveBK_13469, prime_sixtyFiveBK_370871, prime_sixtyFiveBK_6277129993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504042 : Nat.totient 76847347466683449388238504042 = 32550366620402065003274880000 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (101, 1), (114400141, 1), (17783176784356463, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_11, prime_sixtyFiveBK_17, prime_sixtyFiveBK_101, prime_sixtyFiveBK_114400141, prime_sixtyFiveBK_17783176784356463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504043 : Nat.totient 76847347466683449388238504043 = 46296348490808819295717394944 := by
  rw [← show ((([(3, 2), (19, 1), (23, 1), (383, 1), (10247, 1), (16183, 1), (307645375274137, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_19, prime_sixtyFiveBK_23, prime_sixtyFiveBK_383, prime_sixtyFiveBK_10247, prime_sixtyFiveBK_16183, prime_sixtyFiveBK_307645375274137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504044 : Nat.totient 76847347466683449388238504044 = 37493023949434700303078338560 := by
  rw [← show ((([(2, 2), (43, 1), (1021, 1), (118057, 1), (179061577, 1), (20700486133, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_43, prime_sixtyFiveBK_1021, prime_sixtyFiveBK_118057, prime_sixtyFiveBK_179061577, prime_sixtyFiveBK_20700486133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504045 : Nat.totient 76847347466683449388238504045 = 61462682968780294772953740864 := by
  rw [← show ((([(5, 1), (4093, 1), (351707, 1), (10676677398239407559, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_4093, prime_sixtyFiveBK_351707, prime_sixtyFiveBK_10676677398239407559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504046 : Nat.totient 76847347466683449388238504046 = 24659218114700090345907609600 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (139, 1), (191, 1), (1117, 1), (570052909, 1), (18478949033, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_41, prime_sixtyFiveBK_139, prime_sixtyFiveBK_191, prime_sixtyFiveBK_1117, prime_sixtyFiveBK_570052909, prime_sixtyFiveBK_18478949033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504047 : Nat.totient 76847347466683449388238504047 = 63597804727150793527179639552 := by
  rw [← show ((([(7, 1), (29, 1), (872839733, 1), (433708901637323353, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_7, prime_sixtyFiveBK_29, prime_sixtyFiveBK_872839733, prime_sixtyFiveBK_433708901637323353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504048 : Nat.totient 76847347466683449388238504048 = 38420386565302628709689078784 := by
  rw [← show ((([(2, 4), (11689, 1), (13421479943, 1), (30614779342489, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_11689, prime_sixtyFiveBK_13421479943, prime_sixtyFiveBK_30614779342489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504049 : Nat.totient 76847347466683449388238504049 = 50734171142688702369269316096 := by
  rw [← show ((([(3, 1), (103, 1), (139218845869, 1), (1786373933899169, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_103, prime_sixtyFiveBK_139218845869, prime_sixtyFiveBK_1786373933899169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504050 : Nat.totient 76847347466683449388238504050 = 28331515485228424451902617600 := by
  rw [← show ((([(2, 1), (5, 2), (13, 1), (827, 1), (6277, 1), (6971, 1), (3267102831286793, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_13, prime_sixtyFiveBK_827, prime_sixtyFiveBK_6277, prime_sixtyFiveBK_6971, prime_sixtyFiveBK_3267102831286793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504051 : Nat.totient 76847347466683449388238504051 = 76792965861762796992801840000 := by
  rw [← show ((([(1439, 1), (78541, 1), (139716949, 1), (4866565441501, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_1439, prime_sixtyFiveBK_78541, prime_sixtyFiveBK_139716949, prime_sixtyFiveBK_4866565441501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504052 : Nat.totient 76847347466683449388238504052 = 25615779955003809017092520640 := by
  rw [← show ((([(2, 2), (3, 4), (10302179, 1), (546889667, 1), (42097379461, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_10302179, prime_sixtyFiveBK_546889667, prime_sixtyFiveBK_42097379461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504053 : Nat.totient 76847347466683449388238504053 = 69861224969712226716580458220 := by
  rw [← show ((([(11, 1), (6986122496971222671658045823, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_11, prime_sixtyFiveBK_6986122496971222671658045823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504054 : Nat.totient 76847347466683449388238504054 = 31621208722353380635408108800 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (127, 1), (52995497, 1), (90201019, 1), (291665471, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_7, prime_sixtyFiveBK_31, prime_sixtyFiveBK_127, prime_sixtyFiveBK_52995497, prime_sixtyFiveBK_90201019, prime_sixtyFiveBK_291665471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504055 : Nat.totient 76847347466683449388238504055 = 40985251855656129895390447008 := by
  rw [← show ((([(3, 1), (5, 1), (323801999, 1), (15821880388634959063, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_323801999, prime_sixtyFiveBK_15821880388634959063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504056 : Nat.totient 76847347466683449388238504056 = 38412578223989592935067389952 := by
  rw [← show ((([(2, 3), (3463, 1), (1770025793, 1), (1567136435847673, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3463, prime_sixtyFiveBK_1770025793, prime_sixtyFiveBK_1567136435847673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504057 : Nat.totient 76847347466683449388238504057 = 76338539117942933009559018240 := by
  rw [← show ((([(193, 1), (691, 1), (576226895515873588538339, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_193, prime_sixtyFiveBK_691, prime_sixtyFiveBK_576226895515873588538339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504058 : Nat.totient 76847347466683449388238504058 = 25615712650313361193966559232 := by
  rw [← show ((([(2, 1), (3, 1), (366787, 1), (167437146197, 1), (208550811137, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_366787, prime_sixtyFiveBK_167437146197, prime_sixtyFiveBK_208550811137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504059 : Nat.totient 76847347466683449388238504059 = 72177887243133255087105638400 := by
  rw [← show ((([(17, 1), (641, 1), (3163, 1), (5407, 1), (6448807, 1), (63942113881, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_17, prime_sixtyFiveBK_641, prime_sixtyFiveBK_3163, prime_sixtyFiveBK_5407, prime_sixtyFiveBK_6448807, prime_sixtyFiveBK_63942113881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504060 : Nat.totient 76847347466683449388238504060 = 30619332168071918856928002048 := by
  rw [← show ((([(2, 2), (5, 1), (257, 1), (587518747, 1), (25447436166047657, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_257, prime_sixtyFiveBK_587518747, prime_sixtyFiveBK_25447436166047657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504061 : Nat.totient 76847347466683449388238504061 = 43912769980961971078993430856 := by
  rw [← show ((([(3, 2), (7, 1), (1219799166137832529972039747, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_7, prime_sixtyFiveBK_1219799166137832529972039747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504062 : Nat.totient 76847347466683449388238504062 = 36401375115797423394428765064 := by
  rw [← show ((([(2, 1), (19, 1), (2022298617544301299690486949, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_19, prime_sixtyFiveBK_2022298617544301299690486949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504063 : Nat.totient 76847347466683449388238504063 = 70258852242769628112100328448 := by
  rw [← show ((([(13, 2), (113, 1), (1423, 1), (2827866046102521442873, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_13, prime_sixtyFiveBK_113, prime_sixtyFiveBK_1423, prime_sixtyFiveBK_2827866046102521442873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504064 : Nat.totient 76847347466683449388238504064 = 23287074989884822309737000960 := by
  rw [← show ((([(2, 7), (3, 1), (11, 1), (1326494527573, 1), (13715116766557, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_11, prime_sixtyFiveBK_1326494527573, prime_sixtyFiveBK_13715116766557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504065 : Nat.totient 76847347466683449388238504065 = 61477877963747942387009425392 := by
  rw [← show ((([(5, 1), (6404734807, 1), (2399704274490609659, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_6404734807, prime_sixtyFiveBK_2399704274490609659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504066 : Nat.totient 76847347466683449388238504066 = 36741163713151168919965394880 := by
  rw [← show ((([(2, 1), (23, 1), (3271, 1), (62533, 1), (399739, 1), (20431710189623, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_23, prime_sixtyFiveBK_3271, prime_sixtyFiveBK_62533, prime_sixtyFiveBK_399739, prime_sixtyFiveBK_20431710189623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504067 : Nat.totient 76847347466683449388238504067 = 50391703149951907725115852800 := by
  rw [← show ((([(3, 1), (61, 1), (471436481, 1), (890747486454447829, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_61, prime_sixtyFiveBK_471436481, prime_sixtyFiveBK_890747486454447829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504068 : Nat.totient 76847347466683449388238504068 = 32932921732994832013013487120 := by
  rw [← show ((([(2, 2), (7, 2), (19891, 1), (19711341983884478927563, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_7, prime_sixtyFiveBK_19891, prime_sixtyFiveBK_19711341983884478927563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504069 : Nat.totient 76847347466683449388238504069 = 76276418571347503951782512640 := by
  rw [← show ((([(137, 1), (7753, 1), (477469, 1), (151528160296014841, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_137, prime_sixtyFiveBK_7753, prime_sixtyFiveBK_477469, prime_sixtyFiveBK_151528160296014841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504070 : Nat.totient 76847347466683449388238504070 = 20486440471649508753302741760 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (3313, 1), (257729977753239592810271, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_3313, prime_sixtyFiveBK_257729977753239592810271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504071 : Nat.totient 76847347466683449388238504071 = 76845760137919136425823644792 := by
  rw [← show ((([(48413, 1), (1587328764312962414810867, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_48413, prime_sixtyFiveBK_1587328764312962414810867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504072 : Nat.totient 76847347466683449388238504072 = 37385196064873029432116028864 := by
  rw [← show ((([(2, 3), (37, 1), (259619417117173815500805757, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_37, prime_sixtyFiveBK_259619417117173815500805757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504073 : Nat.totient 76847347466683449388238504073 = 51231506316743979902892606768 := by
  rw [← show ((([(3, 1), (873349, 1), (29330522493177965657959, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_873349, prime_sixtyFiveBK_29330522493177965657959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504074 : Nat.totient 76847347466683449388238504074 = 36971283992842194137802316800 := by
  rw [← show ((([(2, 1), (53, 1), (59, 1), (419, 1), (6478201, 1), (4526917323581449, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_53, prime_sixtyFiveBK_59, prime_sixtyFiveBK_419, prime_sixtyFiveBK_6478201, prime_sixtyFiveBK_4526917323581449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504075 : Nat.totient 76847347466683449388238504075 = 47904839979231241177083741600 := by
  rw [← show ((([(5, 2), (7, 1), (11, 1), (39920699982692700980903119, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_7, prime_sixtyFiveBK_11, prime_sixtyFiveBK_39920699982692700980903119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504076 : Nat.totient 76847347466683449388238504076 = 21265525236879698684297084928 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (17, 1), (29, 1), (97, 1), (1502322037, 1), (6856817521973, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_13, prime_sixtyFiveBK_17, prime_sixtyFiveBK_29, prime_sixtyFiveBK_97, prime_sixtyFiveBK_1502322037, prime_sixtyFiveBK_6856817521973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504077 : Nat.totient 76847347466683449388238504077 = 75211735739222868903576618480 := by
  rw [← show ((([(47, 1), (135271, 1), (13036379, 1), (927191293920799, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_47, prime_sixtyFiveBK_135271, prime_sixtyFiveBK_13036379, prime_sixtyFiveBK_927191293920799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504078 : Nat.totient 76847347466683449388238504078 = 37953522038608709827479863040 := by
  rw [← show ((([(2, 1), (89, 1), (991, 1), (431077, 1), (1010602511033954093, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_89, prime_sixtyFiveBK_991, prime_sixtyFiveBK_431077, prime_sixtyFiveBK_1010602511033954093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504079 : Nat.totient 76847347466683449388238504079 = 51231564971641084843287071928 := by
  rw [← show ((([(3, 3), (8333206639, 1), (341548959196715443, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_8333206639, prime_sixtyFiveBK_341548959196715443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504080 : Nat.totient 76847347466683449388238504080 = 30718754751532237140180971520 := by
  rw [← show ((([(2, 4), (5, 1), (1523, 1), (28334881, 1), (22259612420131927, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_1523, prime_sixtyFiveBK_28334881, prime_sixtyFiveBK_22259612420131927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504081 : Nat.totient 76847347466683449388238504081 = 71600190705932698912521640320 := by
  rw [← show ((([(19, 1), (67, 1), (619, 1), (767843, 1), (127009848945544441, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_19, prime_sixtyFiveBK_67, prime_sixtyFiveBK_619, prime_sixtyFiveBK_767843, prime_sixtyFiveBK_127009848945544441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504082 : Nat.totient 76847347466683449388238504082 = 21956203802744445738441702720 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (121181, 1), (21759444947, 1), (693900573203, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_7, prime_sixtyFiveBK_121181, prime_sixtyFiveBK_21759444947, prime_sixtyFiveBK_693900573203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504083 : Nat.totient 76847347466683449388238504083 = 76847129356255827342876799200 := by
  rw [← show ((([(352333, 1), (212428782581, 1), (1026744061571, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_352333, prime_sixtyFiveBK_212428782581, prime_sixtyFiveBK_1026744061571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504084 : Nat.totient 76847347466683449388238504084 = 38184288742404845875121925120 := by
  rw [← show ((([(2, 2), (281, 1), (373, 1), (37624152029, 1), (4871772705773, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_281, prime_sixtyFiveBK_373, prime_sixtyFiveBK_37624152029, prime_sixtyFiveBK_4871772705773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504085 : Nat.totient 76847347466683449388238504085 = 39663147079578554522961808320 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (165263112831577310512340869, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_31, prime_sixtyFiveBK_165263112831577310512340869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504086 : Nat.totient 76847347466683449388238504086 = 34784397837575301067147312800 := by
  rw [← show ((([(2, 1), (11, 1), (239, 1), (565997, 1), (25822255296972509611, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_11, prime_sixtyFiveBK_239, prime_sixtyFiveBK_565997, prime_sixtyFiveBK_25822255296972509611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504087 : Nat.totient 76847347466683449388238504087 = 73229463269443105486239752640 := by
  rw [← show ((([(41, 1), (43, 1), (43588966231811372313237949, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_41, prime_sixtyFiveBK_43, prime_sixtyFiveBK_43588966231811372313237949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504088 : Nat.totient 76847347466683449388238504088 = 25613504112493649138768830464 := by
  rw [← show ((([(2, 3), (3, 2), (11243, 1), (92766319649, 1), (1023349183697, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_11243, prime_sixtyFiveBK_92766319649, prime_sixtyFiveBK_1023349183697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504089 : Nat.totient 76847347466683449388238504089 = 58156519397691778241664245760 := by
  rw [← show ((([(7, 1), (13, 1), (23, 1), (26449, 1), (123057481, 1), (11280864321317, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_7, prime_sixtyFiveBK_13, prime_sixtyFiveBK_23, prime_sixtyFiveBK_26449, prime_sixtyFiveBK_123057481, prime_sixtyFiveBK_11280864321317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504090 : Nat.totient 76847347466683449388238504090 = 30358403953429890060867760704 := by
  rw [← show ((([(2, 1), (5, 1), (83, 1), (3019, 1), (238639, 1), (128512761453882103, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_5, prime_sixtyFiveBK_83, prime_sixtyFiveBK_3019, prime_sixtyFiveBK_238639, prime_sixtyFiveBK_128512761453882103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504091 : Nat.totient 76847347466683449388238504091 = 51231561344307791393763997440 := by
  rw [← show ((([(3, 1), (14099857, 1), (1816740587432516736121, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_14099857, prime_sixtyFiveBK_1816740587432516736121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504092 : Nat.totient 76847347466683449388238504092 = 37994098233660317102789463168 := by
  rw [← show ((([(2, 2), (163, 1), (197, 1), (598294567801403330542793, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_163, prime_sixtyFiveBK_197, prime_sixtyFiveBK_598294567801403330542793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504093 : Nat.totient 76847347466683449388238504093 = 72326873320043443707424148736 := by
  rw [← show ((([(17, 1), (2173727, 1), (8342693, 1), (249269244833239, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_17, prime_sixtyFiveBK_2173727, prime_sixtyFiveBK_8342693, prime_sixtyFiveBK_249269244833239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504094 : Nat.totient 76847347466683449388238504094 = 25614704973120752658579092928 := by
  rw [← show ((([(2, 1), (3, 1), (23773, 1), (538757886865235416847113, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_23773, prime_sixtyFiveBK_538757886865235416847113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504095 : Nat.totient 76847347466683449388238504095 = 61247685409724350560881808000 := by
  rw [← show ((([(5, 1), (311, 1), (2551, 1), (7213, 1), (2685790277927939983, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_5, prime_sixtyFiveBK_311, prime_sixtyFiveBK_2551, prime_sixtyFiveBK_7213, prime_sixtyFiveBK_2685790277927939983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504096 : Nat.totient 76847347466683449388238504096 = 32934577485712330268004920064 := by
  rw [← show ((([(2, 5), (7, 1), (3747558555773, 1), (91544537695823, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_7, prime_sixtyFiveBK_3747558555773, prime_sixtyFiveBK_91544537695823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504097 : Nat.totient 76847347466683449388238504097 = 46574149979782933286087414880 := by
  rw [← show ((([(3, 2), (11, 1), (1855059384637, 1), (418442578941319, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_3, prime_sixtyFiveBK_11, prime_sixtyFiveBK_1855059384637, prime_sixtyFiveBK_418442578941319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504098 : Nat.totient 76847347466683449388238504098 = 38407291832811737853411831360 := by
  rw [← show ((([(2, 1), (2347, 1), (3657347, 1), (4476304578003354961, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_2347, prime_sixtyFiveBK_3657347, prime_sixtyFiveBK_4476304578003354961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504099 : Nat.totient 76847347466683449388238504099 = 76617102990005862369301816992 := by
  rw [← show ((([(379, 1), (2789, 1), (72701129358252926724229, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_379, prime_sixtyFiveBK_2789, prime_sixtyFiveBK_72701129358252926724229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyFiveBK_76847347466683449388238504100 : Nat.totient 76847347466683449388238504100 = 19346892613420250966376038400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (19, 1), (367, 1), (1361, 1), (394367, 1), (68443036627897, 1)] : List FactorBlock).map factorBlockValue).prod) = 76847347466683449388238504100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyFiveBK_2, prime_sixtyFiveBK_3, prime_sixtyFiveBK_5, prime_sixtyFiveBK_19, prime_sixtyFiveBK_367, prime_sixtyFiveBK_1361, prime_sixtyFiveBK_394367, prime_sixtyFiveBK_68443036627897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyFiveBK : certifiedKill 1 76847347466683449388238503999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyFiveBK_76847347466683449388238504000, phi_sixtyFiveBK_76847347466683449388238504001, phi_sixtyFiveBK_76847347466683449388238504002,
    phi_sixtyFiveBK_76847347466683449388238504003, phi_sixtyFiveBK_76847347466683449388238504004, phi_sixtyFiveBK_76847347466683449388238504005,
    phi_sixtyFiveBK_76847347466683449388238504006, phi_sixtyFiveBK_76847347466683449388238504007, phi_sixtyFiveBK_76847347466683449388238504008,
    phi_sixtyFiveBK_76847347466683449388238504009, phi_sixtyFiveBK_76847347466683449388238504010, phi_sixtyFiveBK_76847347466683449388238504011,
    phi_sixtyFiveBK_76847347466683449388238504012, phi_sixtyFiveBK_76847347466683449388238504013, phi_sixtyFiveBK_76847347466683449388238504014,
    phi_sixtyFiveBK_76847347466683449388238504015, phi_sixtyFiveBK_76847347466683449388238504016, phi_sixtyFiveBK_76847347466683449388238504017,
    phi_sixtyFiveBK_76847347466683449388238504018, phi_sixtyFiveBK_76847347466683449388238504019, phi_sixtyFiveBK_76847347466683449388238504020,
    phi_sixtyFiveBK_76847347466683449388238504021, phi_sixtyFiveBK_76847347466683449388238504022, phi_sixtyFiveBK_76847347466683449388238504023,
    phi_sixtyFiveBK_76847347466683449388238504024, phi_sixtyFiveBK_76847347466683449388238504025, phi_sixtyFiveBK_76847347466683449388238504026,
    phi_sixtyFiveBK_76847347466683449388238504027, phi_sixtyFiveBK_76847347466683449388238504028, phi_sixtyFiveBK_76847347466683449388238504029,
    phi_sixtyFiveBK_76847347466683449388238504030, phi_sixtyFiveBK_76847347466683449388238504031, phi_sixtyFiveBK_76847347466683449388238504032,
    phi_sixtyFiveBK_76847347466683449388238504033, phi_sixtyFiveBK_76847347466683449388238504034, phi_sixtyFiveBK_76847347466683449388238504035,
    phi_sixtyFiveBK_76847347466683449388238504036, phi_sixtyFiveBK_76847347466683449388238504037, phi_sixtyFiveBK_76847347466683449388238504038,
    phi_sixtyFiveBK_76847347466683449388238504039, phi_sixtyFiveBK_76847347466683449388238504040, phi_sixtyFiveBK_76847347466683449388238504041,
    phi_sixtyFiveBK_76847347466683449388238504042, phi_sixtyFiveBK_76847347466683449388238504043, phi_sixtyFiveBK_76847347466683449388238504044,
    phi_sixtyFiveBK_76847347466683449388238504045, phi_sixtyFiveBK_76847347466683449388238504046, phi_sixtyFiveBK_76847347466683449388238504047,
    phi_sixtyFiveBK_76847347466683449388238504048, phi_sixtyFiveBK_76847347466683449388238504049, phi_sixtyFiveBK_76847347466683449388238504050,
    phi_sixtyFiveBK_76847347466683449388238504051, phi_sixtyFiveBK_76847347466683449388238504052, phi_sixtyFiveBK_76847347466683449388238504053,
    phi_sixtyFiveBK_76847347466683449388238504054, phi_sixtyFiveBK_76847347466683449388238504055, phi_sixtyFiveBK_76847347466683449388238504056,
    phi_sixtyFiveBK_76847347466683449388238504057, phi_sixtyFiveBK_76847347466683449388238504058, phi_sixtyFiveBK_76847347466683449388238504059,
    phi_sixtyFiveBK_76847347466683449388238504060, phi_sixtyFiveBK_76847347466683449388238504061, phi_sixtyFiveBK_76847347466683449388238504062,
    phi_sixtyFiveBK_76847347466683449388238504063, phi_sixtyFiveBK_76847347466683449388238504064, phi_sixtyFiveBK_76847347466683449388238504065,
    phi_sixtyFiveBK_76847347466683449388238504066, phi_sixtyFiveBK_76847347466683449388238504067, phi_sixtyFiveBK_76847347466683449388238504068,
    phi_sixtyFiveBK_76847347466683449388238504069, phi_sixtyFiveBK_76847347466683449388238504070, phi_sixtyFiveBK_76847347466683449388238504071,
    phi_sixtyFiveBK_76847347466683449388238504072, phi_sixtyFiveBK_76847347466683449388238504073, phi_sixtyFiveBK_76847347466683449388238504074,
    phi_sixtyFiveBK_76847347466683449388238504075, phi_sixtyFiveBK_76847347466683449388238504076, phi_sixtyFiveBK_76847347466683449388238504077,
    phi_sixtyFiveBK_76847347466683449388238504078, phi_sixtyFiveBK_76847347466683449388238504079, phi_sixtyFiveBK_76847347466683449388238504080,
    phi_sixtyFiveBK_76847347466683449388238504081, phi_sixtyFiveBK_76847347466683449388238504082, phi_sixtyFiveBK_76847347466683449388238504083,
    phi_sixtyFiveBK_76847347466683449388238504084, phi_sixtyFiveBK_76847347466683449388238504085, phi_sixtyFiveBK_76847347466683449388238504086,
    phi_sixtyFiveBK_76847347466683449388238504087, phi_sixtyFiveBK_76847347466683449388238504088, phi_sixtyFiveBK_76847347466683449388238504089,
    phi_sixtyFiveBK_76847347466683449388238504090, phi_sixtyFiveBK_76847347466683449388238504091, phi_sixtyFiveBK_76847347466683449388238504092,
    phi_sixtyFiveBK_76847347466683449388238504093, phi_sixtyFiveBK_76847347466683449388238504094, phi_sixtyFiveBK_76847347466683449388238504095,
    phi_sixtyFiveBK_76847347466683449388238504096, phi_sixtyFiveBK_76847347466683449388238504097, phi_sixtyFiveBK_76847347466683449388238504098,
    phi_sixtyFiveBK_76847347466683449388238504099, phi_sixtyFiveBK_76847347466683449388238504100]

end TotientTailPeriodKiller
end Erdos249257
